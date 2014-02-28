/*
 * Copyright 2012-2013 Andrew Smith
 * Copyright 2012 Xiangfu <xiangfu@openmobilefree.com>
 * Copyright 2013 Con Kolivas <kernel@kolivas.org>
 *
 * This program is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License as published by the Free
 * Software Foundation; either version 3 of the License, or (at your option)
 * any later version.  See COPYING for more details.
 */

/*
 * Those code should be works fine with V2 and V3 bitstream of dualminer.
 * Operation:
 *   No detection implement.
 *   Input: 64B = 32B midstate + 20B fill bytes + last 12 bytes of block head.
 *   Return: send back 32bits immediately when dualminer found a valid nonce.
 *           no query protocol implemented here, if no data send back in ~11.3
 *           seconds (full cover time on 32bit nonce range by 380MH/s speed)
 *           just send another work.
 * Notice:
 *   1. dualminer will start calculate when you push a work to them, even they
 *      are busy.
 *   2. The 2 FPGAs on dualminer will distribute the job, one will calculate the
 *      0 ~ 7FFFFFFF, another one will cover the 80000000 ~ FFFFFFFF.
 *   3. It's possible for 2 FPGAs both find valid nonce in the meantime, the 2
 *      valid nonce will all be send back.
 *   4. dualminer will stop work when: a valid nonce has been found or 32 bits
 *      nonce range is completely calculated.
 */


#include <float.h>
#include <limits.h>
#include <pthread.h>
#include <stdint.h>
#include <stdio.h>
#include <strings.h>
#include <sys/time.h>
#include <unistd.h>

#include "config.h"

#ifdef WIN32
#include <windows.h>
#endif

#include "compat.h"
#include "miner.h"
#include "usbutils.h"
#include "driver-dualminer.h"

// The serial I/O speed - Linux uses a define 'B115200' in bits/termios.h
#define DUALMINER_IO_SPEED 115200

// The size of a successful nonce read
#define DUALMINER_READ_SIZE 4

#define AMU_PREF_PACKET 256
#define BLT_PREF_PACKET 512
#define ICA_PREF_PACKET 256

// Ensure the sizes are correct for the Serial read
#if (DUALMINER_READ_SIZE != 4)
#error DUALMINER_READ_SIZE must be 4
#endif
#define ASSERT1(condition) __maybe_unused static char sizeof_uint32_t_must_be_4[(condition)?1:-1]
ASSERT1(sizeof(uint32_t) == 4);

// TODO: USB? Different calculation? - see usbstats to work it out e.g. 1/2 of normal send time
//  or even use that number? 1/2
// #define DUALMINER_READ_TIME(baud) ((double)DUALMINER_READ_SIZE * (double)8.0 / (double)(baud))
// maybe 1ms?
#define DUALMINER_READ_TIME(baud) (0.001)

// USB ms timeout to wait - user specified timeouts are multiples of this
#define DUALMINER_WAIT_TIMEOUT 100
#define DUALMINER_CMR2_TIMEOUT 1

// Defined in multiples of DUALMINER_WAIT_TIMEOUT
// Must of course be greater than DUALMINER_READ_COUNT_TIMING/DUALMINER_WAIT_TIMEOUT
// There's no need to have this bigger, since the overhead/latency of extra work
// is pretty small once you get beyond a 10s nonce range time and 10s also
// means that nothing slower than 429MH/s can go idle so most dualminer devices
// will always mine without idling
#define DUALMINER_READ_TIME_LIMIT_MAX 100

// In timing mode: Default starting value until an estimate can be obtained
// 5000 ms allows for up to a ~840MH/s device
#define DUALMINER_READ_COUNT_TIMING	5000
#define DUALMINER_READ_COUNT_MIN		DUALMINER_WAIT_TIMEOUT
#define SECTOMS(s)	((int)((s) * 1000))
// How many ms below the expected completion time to abort work
// extra in case the last read is delayed
#define DUALMINER_READ_REDUCE	((int)(DUALMINER_WAIT_TIMEOUT * 1.5))

// For a standard dualminer REV3 (to 5 places)
// Since this rounds up a the last digit - it is a slight overestimate
// Thus the hash rate will be a VERY slight underestimate
// (by a lot less than the displayed accuracy)
// Minor inaccuracy of these numbers doesn't affect the work done,
// only the displayed MH/s
#define DUALMINER_REV3_HASH_TIME 0.0000000026316
#define LANCELOT_HASH_TIME 0.0000000025000
#define ASICMINERUSB_HASH_TIME 0.0000000029761
// TODO: What is it?
#define CAIRNSMORE1_HASH_TIME 0.0000000027000
// Per FPGA
#define CAIRNSMORE2_HASH_TIME 0.0000000066600
#define NANOSEC 1000000000.0

// dualminer Rev3 doesn't send a completion message when it finishes
// the full nonce range, so to avoid being idle we must abort the
// work (by starting a new work item) shortly before it finishes
//
// Thus we need to estimate 2 things:
//	1) How many hashes were done if the work was aborted
//	2) How high can the timeout be before the dualminer is idle,
//		to minimise the number of work items started
//	We set 2) to 'the calculated estimate' - DUALMINER_READ_REDUCE
//	to ensure the estimate ends before idle
//
// The simple calculation used is:
//	Tn = Total time in seconds to calculate n hashes
//	Hs = seconds per hash
//	Xn = number of hashes
//	W  = code/usb overhead per work
//
// Rough but reasonable estimate:
//	Tn = Hs * Xn + W	(of the form y = mx + b)
//
// Thus:
//	Line of best fit (using least squares)
//
//	Hs = (n*Sum(XiTi)-Sum(Xi)*Sum(Ti))/(n*Sum(Xi^2)-Sum(Xi)^2)
//	W = Sum(Ti)/n - (Hs*Sum(Xi))/n
//
// N.B. W is less when aborting work since we aren't waiting for the reply
//	to be transferred back (DUALMINER_READ_TIME)
//	Calculating the hashes aborted at n seconds is thus just n/Hs
//	(though this is still a slight overestimate due to code delays)
//

// Both below must be exceeded to complete a set of data
// Minimum how long after the first, the last data point must be
#define HISTORY_SEC 60
// Minimum how many points a single DUALMINER_HISTORY should have
#define MIN_DATA_COUNT 5
// The value MIN_DATA_COUNT used is doubled each history until it exceeds:
#define MAX_MIN_DATA_COUNT 100

static struct timeval history_sec = { HISTORY_SEC, 0 };

// Store the last INFO_HISTORY data sets
// [0] = current data, not yet ready to be included as an estimate
// Each new data set throws the last old set off the end thus
// keeping a ongoing average of recent data
#define INFO_HISTORY 10

struct DUALMINER_HISTORY {
	struct timeval finish;
	double sumXiTi;
	double sumXi;
	double sumTi;
	double sumXi2;
	uint32_t values;
	uint32_t hash_count_min;
	uint32_t hash_count_max;
};

enum timing_mode { MODE_DEFAULT, MODE_SHORT, MODE_LONG, MODE_VALUE };

static const char *MODE_DEFAULT_STR = "default";
static const char *MODE_SHORT_STR = "short";
static const char *MODE_SHORT_STREQ = "short=";
static const char *MODE_LONG_STR = "long";
static const char *MODE_LONG_STREQ = "long=";
static const char *MODE_VALUE_STR = "value";
static const char *MODE_UNKNOWN_STR = "unknown";

struct DUALMINER_INFO {
	int intinfo;

	// time to calculate the golden_ob
	uint64_t golden_hashes;
	struct timeval golden_tv;

	struct DUALMINER_HISTORY history[INFO_HISTORY+1];
	uint32_t min_data_count;

	int timeout;

	// seconds per Hash
	double Hs;
	// ms til we abort
	int read_time;
	// ms limit for (short=/long=) read_time
	int read_time_limit;

	enum timing_mode timing_mode;
	bool do_dualminer_timing;

	double fullnonce;
	int count;
	double W;
	uint32_t values;
	uint64_t hash_count_range;

	// Determine the cost of history processing
	// (which will only affect W)
	uint64_t history_count;
	struct timeval history_time;

	// dualminer-options
	int baud;
	int work_division;
	int fpga_count;
	uint32_t nonce_mask;

	bool initialised;
};

#define END_CONDITION 0x0000ffff

static int option_offset = -1;
static int opt_btc_number = 160;
static int opt_pll_freq = 400;

static void _transfer(struct cgpu_info *dualminer, uint8_t request_type, uint8_t bRequest, uint16_t wValue, uint16_t wIndex, uint32_t *data, int siz, enum usb_cmds cmd)
{
	int err;

	err = usb_transfer_data(dualminer, request_type, bRequest, wValue, wIndex, data, siz, cmd);

	applog(LOG_DEBUG, "%s: cgid %d %s got err %d",
			dualminer->drv->name, dualminer->cgminer_id,
			usb_cmdname(cmd), err);
}

#define transfer(dualminer, request_type, bRequest, wValue, wIndex, cmd) \
		_transfer(dualminer, request_type, bRequest, wValue, wIndex, NULL, 0, cmd)


static int dualminer_set_dtr(struct cgpu_info *dualminer, int state)
{
	unsigned short usb_val;

	if (dualminer == NULL || dualminer->usbdev == NULL)
		return -2;

	if (state)
		usb_val = SIO_SET_DTR_LOW;
	else
		usb_val = SIO_SET_DTR_HIGH;
	if (libusb_control_transfer(dualminer->usbdev->handle, FTDI_TYPE_OUT, SIO_SET_MODEM_CTRL_REQUEST, usb_val, 0, NULL, 0, 200) < 0)
		return -1;

	return 0;
}

//mast after usb_init
static int dualminer_get_cts(struct cgpu_info *dualminer)
{
	char usb_val[2];
	unsigned short status;
	if(dualminer->usbdev->handle == NULL)
	{
		return -1;
	}
	if (libusb_control_transfer(dualminer->usbdev->handle, FTDI_TYPE_IN, SIO_POLL_MODEM_STATUS_REQUEST, 0, 1, (unsigned char *)usb_val, 2, 200) != 2)
	{
		return -1;
	}
	status = (usb_val[1] << 8) | (usb_val[0] & 0xFF);
	return ((status & 0x10) ? 0 : 1); 
}

static int dualminer_set_rts_status(struct cgpu_info *dualminer, unsigned int state)
{
	unsigned short usb_val;
	if(dualminer->usbdev->handle == NULL)
	{
		return -1;
	}
	if(state)
	{
		usb_val = SIO_SET_RTS_HIGH;
	}
	else
	{
		usb_val = SIO_SET_RTS_LOW;
	}

	if (libusb_control_transfer(dualminer->usbdev->handle, FTDI_TYPE_OUT, SIO_SET_MODEM_CTRL_REQUEST, usb_val, 2, NULL, 0, 200) < 0)
	{
		return -1;
	}
	return 0;	
}

static void dualminer_send_cmds(struct cgpu_info *dualminer, const char *cmds[], int interface)
{
	int i = 0;
	int err;
	int amount = 0;
	unsigned char ob_bin[32];
	for(i = 0 ;; i++)
	{
		memset(ob_bin, 0, sizeof(ob_bin));
		if (cmds[i][0] == NULL)
		{
			break;
		}
		hex2bin(ob_bin, cmds[i], sizeof(ob_bin));

		err = usb_write_ii(dualminer, interface, (char *)ob_bin, 8, &amount, C_SENDTESTWORK);
		if (err != LIBUSB_SUCCESS || amount != 8)
		{
			applog(LOG_ERR, "Write to USB error: %d, amount = %d", err, amount);
			return;
		}
		usleep(DEFAULT_DELAY_TIME);
	}
}

static void dualminer_set_pll_freq(struct cgpu_info *dualminer, int pll_freq)
{
	switch(pll_freq)
	{
	case 400:
		dualminer_send_cmds(dualminer, pll_freq_400M_cmd, FTDI_INTERFACE_A);
		break;
	case 500:
		dualminer_send_cmds(dualminer, pll_freq_500M_cmd, FTDI_INTERFACE_A);
		break;
	case 550:
		dualminer_send_cmds(dualminer, pll_freq_550M_cmd, FTDI_INTERFACE_A);
		break;
	case 600:
		dualminer_send_cmds(dualminer, pll_freq_600M_cmd, FTDI_INTERFACE_A);
		break;
	case 650:
		dualminer_send_cmds(dualminer, pll_freq_650M_cmd, FTDI_INTERFACE_A);
		break;
	case 700:
		dualminer_send_cmds(dualminer, pll_freq_700M_cmd, FTDI_INTERFACE_A);
		break;
	case 750:
		dualminer_send_cmds(dualminer, pll_freq_750M_cmd, FTDI_INTERFACE_A);
		break;
	case 800:
		dualminer_send_cmds(dualminer, pll_freq_800M_cmd, FTDI_INTERFACE_A);
		break;
	case 850:
		dualminer_send_cmds(dualminer, pll_freq_850M_cmd, FTDI_INTERFACE_A);
		break;
	case 900:
		dualminer_send_cmds(dualminer, pll_freq_900M_cmd, FTDI_INTERFACE_A);
		break;
	case 950:
		dualminer_send_cmds(dualminer, pll_freq_950M_cmd, FTDI_INTERFACE_A);
		break;
	case 1000:
		dualminer_send_cmds(dualminer, pll_freq_1000M_cmd, FTDI_INTERFACE_A);
		break;
	case 1100:
		dualminer_send_cmds(dualminer, pll_freq_1100M_cmd, FTDI_INTERFACE_A);
		break;
	case 1200:
		dualminer_send_cmds(dualminer, pll_freq_1200M_cmd, FTDI_INTERFACE_A);
		break;
	default: return;
	}
}

static int dualminer_open_btc_unit(struct cgpu_info *dualminer, int units)
{
	int i, err, amount;
	unsigned char ob_bin[32];
	if(!units == 0)
	{
		for(i = 0; i <= units; i++)
		{
			memset(ob_bin, 0, sizeof(ob_bin));
			hex2bin(ob_bin, btc_single_open[i], sizeof(ob_bin));
			err = usb_write_ii(dualminer, FTDI_INTERFACE_A, (char *)ob_bin, 8, &amount, C_SENDTESTWORK);
			if (err != LIBUSB_SUCCESS || amount != 8)
			{
				applog(LOG_ERR, "Write to USB error: %d, amount = %d", err, amount);
				return -1;
			}
			usleep(DEFAULT_DELAY_TIME);
		}
		opt_btc_number = units;
		return units;
	}
	opt_btc_number = 0;
	return 0;
}

static void dualminer_initialise(struct cgpu_info *dualminer, int baud)
{
	struct DUALMINER_INFO *info = (struct DUALMINER_INFO *)(dualminer->device_data);
	uint16_t wValue, wIndex;
	enum sub_ident ident;
	int interface;

	if (dualminer->usbinfo.nodev)
		return;
	usb_set_cps(dualminer, baud / 10);
	usb_enable_cps(dualminer);
	ident = usb_ident(dualminer);

	switch (ident) {
		case IDENT_DM:
			transfer(dualminer, FTDI_TYPE_OUT, FTDI_REQUEST_BAUD, 0xC068, 0x201 , C_SETBAUD);
			if (dualminer->usbinfo.nodev)
				return;
             //add by wangzhaofeng
			 if(!opt_dualminer_interface)
			 {
			 //interface b  baund and tx rx purge
			transfer(dualminer, FTDI_TYPE_OUT, FTDI_REQUEST_BAUD, 0xC068, 0x202 , C_SETBAUD);
			if (dualminer->usbinfo.nodev)
				return;
			transfer(dualminer, FTDI_TYPE_OUT, FTDI_REQUEST_RESET, FTDI_VALUE_PURGE_TX, FTDI_INTERFACE_B, C_PURGETX);
			if (dualminer->usbinfo.nodev)
				return;

			transfer(dualminer, FTDI_TYPE_OUT, FTDI_REQUEST_RESET, FTDI_VALUE_PURGE_RX, FTDI_INTERFACE_B, C_PURGERX);
			if (dualminer->usbinfo.nodev)
				return;
			}
			transfer(dualminer, FTDI_TYPE_OUT, FTDI_REQUEST_RESET, FTDI_VALUE_PURGE_TX, FTDI_INTERFACE_A, C_PURGETX);
			if (dualminer->usbinfo.nodev)
				return;

			transfer(dualminer, FTDI_TYPE_OUT, FTDI_REQUEST_RESET, FTDI_VALUE_PURGE_RX, FTDI_INTERFACE_A, C_PURGERX);
			if (dualminer->usbinfo.nodev)
				return;

			

			dualminer_set_dtr(dualminer, 0);
			usleep(DEFAULT_DELAY_TIME);
			dualminer_set_dtr(dualminer, 1);
			usleep(DEFAULT_DELAY_TIME);
             if(!opt_dualminer_interface)
			 {
			dualminer_send_cmds(dualminer, btc_gating, FTDI_INTERFACE_A);
			dualminer_send_cmds(dualminer, btc_init, FTDI_INTERFACE_A);
			dualminer_send_cmds(dualminer, ltc_init, FTDI_INTERFACE_B);
			}
			else
			dualminer_send_cmds(dualminer,ltc_only_init,FTDI_INTERFACE_A);
			if(opt_dualminer_pll != 0)
			{
				dualminer_set_pll_freq(dualminer, opt_dualminer_pll);
				opt_pll_freq = opt_dualminer_pll;
			}
			else
			{
				if(dualminer_get_cts(dualminer) == 0)
				{
					dualminer_send_cmds(dualminer, pll_freq_550M_cmd, FTDI_INTERFACE_A);
					opt_pll_freq = 550;
				}
				else
				{
					dualminer_send_cmds(dualminer, pll_freq_850M_cmd, FTDI_INTERFACE_A);
					opt_pll_freq = 850;
				}
			}
			if(!opt_dualminer_interface)
			dualminer_send_cmds(dualminer, btc_open_nonce_unit, FTDI_INTERFACE_A);
			break;
		default:
			quit(1, "dualminer_intialise() called with invalid %s cgid %i ident=%d",
				dualminer->drv->name, dualminer->cgminer_id, ident);
	}
	info->initialised = true;
}

static void rev(unsigned char *s, size_t l)
{
	size_t i, j;
	unsigned char t;

	for (i = 0, j = l - 1; i < j; i++, j--) {
		t = s[i];
		s[i] = s[j];
		s[j] = t;
	}
}

#define DM_NONCE_ERROR -1
#define DM_NONCE_OK 0
#define DM_NONCE_RESTART 1
#define DM_NONCE_TIMEOUT 2

static int dualminer_get_nonce(struct cgpu_info *dualminer, unsigned char *buf, struct timeval *tv_start, struct timeval *tv_finish, struct thr_info *thr, int read_time)
{
	struct DUALMINER_INFO *info = (struct DUALMINER_INFO *)(dualminer->device_data);
	struct timeval read_start, read_finish;
	int err, amt;
	int rc = 0, delay;
	int read_amount = DUALMINER_READ_SIZE;
	bool first = true;

	cgtime(tv_start);
	while (true) 
	{
		if (dualminer->usbinfo.nodev)
			return DM_NONCE_ERROR;

		cgtime(&read_start);

		err = usb_read_ii_once_timeout(dualminer, (opt_dualminer_interface?0:(opt_scrypt ? 1 : 0)), (char *)buf,
					      DUALMINER_READ_SIZE, &amt, info->timeout, C_GETRESULTS);
		cgtime(&read_finish);
		if (err < 0 && err != LIBUSB_ERROR_TIMEOUT) {
			applog(LOG_ERR, "%s%i: Comms error (rerr=%d amt=%d)",
					dualminer->drv->name, dualminer->device_id, err, amt);
			dev_error(dualminer, REASON_DEV_COMMS_ERROR);
			return DM_NONCE_ERROR;
		}

		if (first)
			copy_time(tv_finish, &read_finish);

		if (amt >= read_amount)
			return DM_NONCE_OK;

		rc = SECTOMS(tdiff(&read_finish, tv_start));
		if (rc >= read_time) {
			if (amt > 0)
				applog(LOG_DEBUG, "dualminer Read: Timeout reading for %d ms", rc);
			else
				applog(LOG_DEBUG, "dualminer Read: No data for %d ms", rc);
			return DM_NONCE_TIMEOUT;
		}

		if (thr && thr->work_restart) {
			applog(LOG_DEBUG, "dualminer Read: Work restart at %d ms", rc);
			return DM_NONCE_RESTART;
		}

		if (amt > 0) {
			buf += amt;
			read_amount -= amt;
			first = false;
		}

		if (info->timeout < DUALMINER_WAIT_TIMEOUT) {
			delay = DUALMINER_WAIT_TIMEOUT - rc;
			if (delay > 0) {
				cgsleep_ms(delay);

				if (thr && thr->work_restart) {
					applog(LOG_DEBUG, "dualminer Read: Work restart at %d ms", rc);
					return DM_NONCE_RESTART;
				}
			}
		}
	}
}

static const char *timing_mode_str(enum timing_mode timing_mode)
{
	switch(timing_mode) {
	case MODE_DEFAULT:
		return MODE_DEFAULT_STR;
	case MODE_SHORT:
		return MODE_SHORT_STR;
	case MODE_LONG:
		return MODE_LONG_STR;
	case MODE_VALUE:
		return MODE_VALUE_STR;
	default:
		return MODE_UNKNOWN_STR;
	}
}


static uint32_t mask(int work_division)
{
	uint32_t nonce_mask = 0x7fffffff;

	// yes we can calculate these, but this way it's easy to see what they are
	switch (work_division) {
	case 1:
		nonce_mask = 0xffffffff;
		break;
	case 2:
		nonce_mask = 0x7fffffff;
		break;
	case 4:
		nonce_mask = 0x3fffffff;
		break;
	case 8:
		nonce_mask = 0x1fffffff;
		break;
	default: break;
	}

	return nonce_mask;
}

static bool dualminer_detect_one(struct libusb_device *dev, struct usb_find_devices *found)
{
	int this_option_offset = ++option_offset;
	struct DUALMINER_INFO *info;
	struct timeval tv_start, tv_finish;

	unsigned char ob_bin[64], nonce_bin[DUALMINER_READ_SIZE], scrypt_bin[160];
	char *nonce_hex;
	int baud, uninitialised_var(work_division), uninitialised_var(fpga_count);
	struct cgpu_info *dualminer;
	int ret, err, amount, tries;
	enum sub_ident ident;
	bool ok;
	baud = DUALMINER_IO_SPEED;
	dualminer = usb_alloc_cgpu(&dualminer_drv, 1);

	if (!usb_init(dualminer, dev, found))
		goto shin;
	usb_buffer_enable(dualminer);
	
	opt_scrypt ? hex2bin(scrypt_bin, ltc_golden, sizeof(scrypt_bin)) : hex2bin(ob_bin, btc_golden, sizeof(ob_bin));
	info = (struct DUALMINER_INFO *)calloc(1, sizeof(struct DUALMINER_INFO));
	if (unlikely(!info))
		quit(1, "Failed to malloc DUALMINER_INFO");
	dualminer->device_data = (void *)info;
	ident = usb_ident(dualminer);
	switch (ident) {
		case IDENT_DM:
			info->timeout = DUALMINER_WAIT_TIMEOUT;
			break;
		default:
			quit(1, "%s dualminer_detect_one() invalid %s ident=%d",
				dualminer->drv->dname, dualminer->drv->dname, ident);
	}

	dualminer_initialise(dualminer, baud);

	tries = 1;
	ok = false;
	while (!ok && tries-- > 0) 
	{
		err = usb_write_ii(dualminer, (opt_dualminer_interface? 0:(opt_scrypt ? 1 : 0)), (char *)(opt_scrypt ? scrypt_bin : ob_bin),
			(opt_scrypt ? sizeof(scrypt_bin) : sizeof(ob_bin)), &amount, C_SENDWORK);

		if (err != LIBUSB_SUCCESS || amount != (opt_scrypt ? sizeof(scrypt_bin) : sizeof(ob_bin)))
		{
			continue;
		}
		memset(nonce_bin, 0, sizeof(nonce_bin));
		ret = dualminer_get_nonce(dualminer, nonce_bin, &tv_start, &tv_finish, NULL, 100);
		if (ret != DM_NONCE_OK)
			continue;
		rev(nonce_bin, 4);

		nonce_hex = bin2hex(nonce_bin, sizeof(nonce_bin));
		if (strncmp(nonce_hex, (opt_scrypt ? ltc_golden_nonce : btc_golden_nonce), 8) == 0)
		{
			ok = true;
			applog(LOG_NOTICE, "\033[1;32mdualminer Detect: Test Success at %s: get %s, should: %s\033[0m", 
				dualminer->device_path, nonce_hex, (opt_scrypt ? ltc_golden_nonce : btc_golden_nonce));
		}
		else 
		{
			applog(LOG_ERR, "DualMiner Detect: Test failed at %s: get %s, should: %s",
				dualminer->device_path, nonce_hex, (opt_scrypt ? ltc_golden_nonce : btc_golden_nonce));
		}
		free(nonce_hex);
	}

	if (!ok) 
	{
		if(!opt_scrypt)
			dualminer_send_cmds(dualminer, btc_close_nonce_unit, FTDI_INTERFACE_A);
		goto unshin;
	} 
	else 
	{
		if(!opt_scrypt)
		{
			dualminer_send_cmds(dualminer, btc_close_nonce_unit, FTDI_INTERFACE_A);
			if(opt_dualminer_btc != -1)
			{
				dualminer_open_btc_unit(dualminer, opt_dualminer_btc);
			}
			else
			{
				if(dualminer_get_cts(dualminer) == 0)
				{
					dualminer_open_btc_unit(dualminer, DEFAULT_0_9V_BTC);
				}
				else
				{
					dualminer_open_btc_unit(dualminer, DEFAULT_1_2V_BTC);
				}
			}
		}
		dualminer_set_rts_status(dualminer, RTS_HIGH);
	}

	applog(LOG_DEBUG,
		"dualminer Detect: "
		"Test succeeded at %s: got %s",
			dualminer->device_path, btc_golden_nonce);

	/* We have a real dualminer! */
	if (!add_cgpu(dualminer))
		goto unshin;

	update_usb_stats(dualminer);

	applog(LOG_INFO, "%s%d: Found at %s",
		dualminer->drv->name, dualminer->device_id, dualminer->device_path);

	applog(LOG_DEBUG, "%s%d: Init baud=%d work_division=%d fpga_count=%d",
		dualminer->drv->name, dualminer->device_id, baud, work_division, fpga_count);

	info->baud = baud;
	info->work_division = work_division;
	info->fpga_count = fpga_count;
	info->nonce_mask = mask(2);
	info->golden_hashes = (btc_golden_nonce_val & info->nonce_mask) * 2;
	timersub(&tv_finish, &tv_start, &(info->golden_tv));

	if(opt_scrypt) info->golden_hashes = (double)((50000) * (double)opt_pll_freq) / 600;
	else info->golden_hashes = ((double)opt_btc_number * 1000000000 /160) * (double)opt_pll_freq / 400;

	return true;

unshin:

	usb_uninit(dualminer);
	free(info);
	dualminer->device_data = NULL;

shin:

	dualminer = usb_free_cgpu(dualminer);

	return false;
}

static void dualminer_detect(bool __maybe_unused hotplug)
{
	usb_detect(&dualminer_drv, dualminer_detect_one);
}

static bool dualminer_prepare(__maybe_unused struct thr_info *thr)
{
//	struct cgpu_info *dualminer = thr->cgpu;

	return true;
}

static int64_t dualminer_scanhash(struct thr_info *thr, struct work *work,
				__maybe_unused int64_t max_nonce)
{
	struct cgpu_info *dualminer = thr->cgpu;
	struct DUALMINER_INFO *info = (struct DUALMINER_INFO *)(dualminer->device_data);
	int ret, err, amount;
	unsigned char ob_bin[64], nonce_bin[DUALMINER_READ_SIZE], btc_bin[52], scrypt_bin[160];
	char *ob_hex;
	uint32_t nonce;
	int64_t hash_count;
	struct timeval tv_start, tv_finish, elapsed;
	struct timeval tv_history_start, tv_history_finish;
	double Ti, Xi;
	int curr_hw_errors, i;
	bool was_hw_error;

	struct DUALMINER_HISTORY *history0, *history;
	int count;
	double Hs, W, fullnonce;
	int read_time;
	bool limited;
	int64_t estimate_hashes;
	uint32_t values;
	int64_t hash_count_range;

	usleep(DEFAULT_DELAY_TIME);

	// Device is gone
	if (dualminer->usbinfo.nodev)
		return -1;

	if (!info->initialised)
		dualminer_initialise(dualminer, info->baud);

	elapsed.tv_sec = elapsed.tv_usec = 0;

	if(!opt_scrypt)
	{
		memset(ob_bin, 0, sizeof(ob_bin));
		memcpy(ob_bin, work->midstate, 32);
		memcpy(ob_bin + 52, work->data + 64, 12);

		memset(btc_bin, 0, sizeof(btc_bin));
		btc_bin[0] = 0x55;
		btc_bin[1] = 0xaa;
		btc_bin[2] = 0x0f;
		btc_bin[3] = 0x00;
		memcpy(btc_bin + 8, ob_bin, 32);
		memcpy(btc_bin + 40, ob_bin + 52, 12);	
	}
	else
	{
		if(!opt_dualminer_interface)
		dualminer_send_cmds(dualminer, ltc_init, 1);
		else
		dualminer_send_cmds(dualminer, ltc_restart, 0);
		memset(scrypt_bin, 0, sizeof(scrypt_bin));
		scrypt_bin[0] = 0x55;
		scrypt_bin[1] = 0xaa;
		scrypt_bin[2] = 0x1f;
		scrypt_bin[3] = 0x00;
		memcpy(scrypt_bin + 4, work->target, 32);
		memcpy(scrypt_bin + 36, work->midstate, 32);
		memcpy(scrypt_bin + 68, work->data, 80);		
		scrypt_bin[148] = 0xff;
		scrypt_bin[149] = 0xff;
		scrypt_bin[150] = 0xff;
		scrypt_bin[151] = 0xff;
	}

	// We only want results for the work we are about to send
	usb_buffer_clear(dualminer);
	//add by wangzhaofeng
	err = usb_write_ii(dualminer, (opt_dualminer_interface?0:(opt_scrypt ? 1 : 0)), (char *)(opt_scrypt ? scrypt_bin : btc_bin), 
		(opt_scrypt ? sizeof(scrypt_bin) : sizeof(btc_bin)), &amount, C_SENDWORK);
	if (err < 0 || amount != (opt_scrypt ? sizeof(scrypt_bin) : sizeof(btc_bin))) {
		applog(LOG_ERR, "%s%i: Comms error (werr=%d amt=%d)",
				dualminer->drv->name, dualminer->device_id, err, amount);
		dev_error(dualminer, REASON_DEV_COMMS_ERROR);
		dualminer_initialise(dualminer, info->baud);
		return 0;
	}

	if (opt_debug) {
		ob_hex = bin2hex((void *)(opt_scrypt ? scrypt_bin : btc_bin), (opt_scrypt ? sizeof(scrypt_bin) : sizeof(btc_bin)));
		applog(LOG_DEBUG, "%s%d: sent %s", dualminer->drv->name, dualminer->device_id, ob_hex);
		free(ob_hex);
	}

	/* dualminer will return 4 bytes (DUALMINER_READ_SIZE) nonces or nothing */
	memset(nonce_bin, 0, sizeof(nonce_bin));
	ret = dualminer_get_nonce(dualminer, nonce_bin, &tv_start, &tv_finish, thr, (opt_scrypt ? 11152 * 3 : 11152));
	if (ret == DM_NONCE_ERROR)
		return 0;
	rev(nonce_bin, 4);
	work->blk.nonce = 0xffffffff;

	timersub(&tv_finish, &tv_start, &elapsed);

	// aborted before becoming idle, get new work
	if (ret == DM_NONCE_TIMEOUT || ret == DM_NONCE_RESTART) {
		
		// ONLY up to just when it aborted
		// We didn't read a reply so we don't subtract DUALMINER_READ_TIME
		estimate_hashes = ((double)(elapsed.tv_sec) + ((double)(elapsed.tv_usec))/((double)1000000))*info->golden_hashes;

		// If some Serial-USB delay allowed the full nonce range to
		// complete it can't have done more than a full nonce
		if (unlikely(estimate_hashes > 0xffffffff))
			estimate_hashes = 0xffffffff;

		applog(LOG_DEBUG, "%s%d: no nonce = 0x%08lX hashes (%ld.%06lds)",
				dualminer->drv->name, dualminer->device_id,
				(long unsigned int)estimate_hashes,
				elapsed.tv_sec, elapsed.tv_usec);

		return estimate_hashes;
	}

	memcpy((char *)&nonce, nonce_bin, sizeof(nonce_bin));
	nonce = htobe32(nonce);
	curr_hw_errors = dualminer->hw_errors;
	submit_nonce(thr, work, nonce);
	was_hw_error = (curr_hw_errors < dualminer->hw_errors);
	if (!was_hw_error)
	{
		//do_dualminer_close(thr);
		hash_count = opt_scrypt ? nonce:((double)(((double)nonce)*opt_btc_number)/160);
		info->golden_hashes=(double)hash_count/((double)(elapsed.tv_sec) + ((double)(elapsed.tv_usec))/((double)1000000));	
		applog(LOG_DEBUG, "dualminer hashcount = %d, hashrate=%d, opt_btc_number=%d", hash_count, info->golden_hashes, opt_btc_number);
		
	}
	else
	{
		hash_count = ((double)(elapsed.tv_sec) + ((double)(elapsed.tv_usec))/((double)1000000))*info->golden_hashes;
	}

#if 0
	// This appears to only return zero nonce values
	if (usb_buffer_size(dualminer) > 3) {
		memcpy((char *)&nonce, dualminer->usbdev->buffer, sizeof(nonce_bin));
		nonce = htobe32(nonce);
		applog(LOG_WARNING, "%s%d: attempting to submit 2nd nonce = 0x%08lX",
				dualminer->drv->name, dualminer->device_id,
				(long unsigned int)nonce);
		curr_hw_errors = dualminer->hw_errors;
		submit_nonce(thr, work, nonce);
		was_hw_error = (curr_hw_errors > dualminer->hw_errors);
	}
#endif

	if (opt_debug || info->do_dualminer_timing)
		timersub(&tv_finish, &tv_start, &elapsed);

	applog(LOG_DEBUG, "%s%d: nonce = 0x%08x = 0x%08lX hashes (%ld.%06lds)",
			dualminer->drv->name, dualminer->device_id,
			nonce, (long unsigned int)hash_count,
			elapsed.tv_sec, elapsed.tv_usec);

	// Ignore possible end condition values ... and hw errors
	// TODO: set limitations on calculated values depending on the device
	// to avoid crap values caused by CPU/Task Switching/Swapping/etc
	if (info->do_dualminer_timing
	&&  !was_hw_error
	&&  ((nonce & info->nonce_mask) > END_CONDITION)
	&&  ((nonce & info->nonce_mask) < (info->nonce_mask & ~END_CONDITION))) {
		cgtime(&tv_history_start);

		history0 = &(info->history[0]);

		if (history0->values == 0)
			timeradd(&tv_start, &history_sec, &(history0->finish));

		Ti = (double)(elapsed.tv_sec)
			+ ((double)(elapsed.tv_usec))/((double)1000000)
			- ((double)DUALMINER_READ_TIME(info->baud));
		Xi = (double)hash_count;
		history0->sumXiTi += Xi * Ti;
		history0->sumXi += Xi;
		history0->sumTi += Ti;
		history0->sumXi2 += Xi * Xi;

		history0->values++;

		if (history0->hash_count_max < hash_count)
			history0->hash_count_max = hash_count;
		if (history0->hash_count_min > hash_count || history0->hash_count_min == 0)
			history0->hash_count_min = hash_count;

		if (history0->values >= info->min_data_count
		&&  timercmp(&tv_start, &(history0->finish), >)) {
			for (i = INFO_HISTORY; i > 0; i--)
				memcpy(&(info->history[i]),
					&(info->history[i-1]),
					sizeof(struct DUALMINER_HISTORY));

			// Initialise history0 to zero for summary calculation
			memset(history0, 0, sizeof(struct DUALMINER_HISTORY));

			// We just completed a history data set
			// So now recalc read_time based on the whole history thus we will
			// initially get more accurate until it completes INFO_HISTORY
			// total data sets
			count = 0;
			for (i = 1 ; i <= INFO_HISTORY; i++) {
				history = &(info->history[i]);
				if (history->values >= MIN_DATA_COUNT) {
					count++;

					history0->sumXiTi += history->sumXiTi;
					history0->sumXi += history->sumXi;
					history0->sumTi += history->sumTi;
					history0->sumXi2 += history->sumXi2;
					history0->values += history->values;

					if (history0->hash_count_max < history->hash_count_max)
						history0->hash_count_max = history->hash_count_max;
					if (history0->hash_count_min > history->hash_count_min || history0->hash_count_min == 0)
						history0->hash_count_min = history->hash_count_min;
				}
			}

			// All history data
			Hs = (history0->values*history0->sumXiTi - history0->sumXi*history0->sumTi)
				/ (history0->values*history0->sumXi2 - history0->sumXi*history0->sumXi);
			W = history0->sumTi/history0->values - Hs*history0->sumXi/history0->values;
			hash_count_range = history0->hash_count_max - history0->hash_count_min;
			values = history0->values;
			
			// Initialise history0 to zero for next data set
			memset(history0, 0, sizeof(struct DUALMINER_HISTORY));

			fullnonce = W + Hs * (((double)0xffffffff) + 1);
			read_time = SECTOMS(fullnonce) - DUALMINER_READ_REDUCE;
			if (info->read_time_limit > 0 && read_time > info->read_time_limit) {
				read_time = info->read_time_limit;
				limited = true;
			} else
				limited = false;

			info->Hs = Hs;
			info->read_time = read_time;

			info->fullnonce = fullnonce;
			info->count = count;
			info->W = W;
			info->values = values;
			info->hash_count_range = hash_count_range;

			if (info->min_data_count < MAX_MIN_DATA_COUNT)
				info->min_data_count *= 2;
			else if (info->timing_mode == MODE_SHORT)
				info->do_dualminer_timing = false;

			applog(LOG_WARNING, "%s%d Re-estimate: Hs=%e W=%e read_time=%dms%s fullnonce=%.3fs",
					dualminer->drv->name, dualminer->device_id, Hs, W, read_time,
					limited ? " (limited)" : "", fullnonce);
		}
		info->history_count++;
		cgtime(&tv_history_finish);

		timersub(&tv_history_finish, &tv_history_start, &tv_history_finish);
		timeradd(&tv_history_finish, &(info->history_time), &(info->history_time));
	}

	return hash_count;
}

static struct api_data *dualminer_api_stats(struct cgpu_info *cgpu)
{
	struct api_data *root = NULL;
	struct DUALMINER_INFO *info = (struct DUALMINER_INFO *)(cgpu->device_data);

	// Warning, access to these is not locked - but we don't really
	// care since hashing performance is way more important than
	// locking access to displaying API debug 'stats'
	// If locking becomes an issue for any of them, use copy_data=true also
	root = api_add_int(root, "read_time", &(info->read_time), false);
	root = api_add_int(root, "read_time_limit", &(info->read_time_limit), false);
	root = api_add_double(root, "fullnonce", &(info->fullnonce), false);
	root = api_add_int(root, "count", &(info->count), false);
	root = api_add_hs(root, "Hs", &(info->Hs), false);
	root = api_add_double(root, "W", &(info->W), false);
	root = api_add_uint(root, "total_values", &(info->values), false);
	root = api_add_uint64(root, "range", &(info->hash_count_range), false);
	root = api_add_uint64(root, "history_count", &(info->history_count), false);
	root = api_add_timeval(root, "history_time", &(info->history_time), false);
	root = api_add_uint(root, "min_data_count", &(info->min_data_count), false);
	root = api_add_uint(root, "timing_values", &(info->history[0].values), false);
	root = api_add_const(root, "timing_mode", timing_mode_str(info->timing_mode), false);
	root = api_add_bool(root, "is_timing", &(info->do_dualminer_timing), false);
	root = api_add_int(root, "baud", &(info->baud), false);
	root = api_add_int(root, "work_division", &(info->work_division), false);
	root = api_add_int(root, "fpga_count", &(info->fpga_count), false);

	return root;
}

static void dualminer_shutdown(__maybe_unused struct thr_info *thr)
{
	dualminer_set_dtr(thr->cgpu, 0);
	dualminer_set_rts_status(thr->cgpu, RTS_LOW);
}

struct device_drv dualminer_drv = {
	.drv_id = DRIVER_dualminer,
	.dname = "DualMiner",
	.name = "DM",
	.drv_detect = dualminer_detect,
	.get_api_stats = dualminer_api_stats,
	.thread_prepare = dualminer_prepare,
	.scanhash = dualminer_scanhash,
	.thread_shutdown = dualminer_shutdown,
};
