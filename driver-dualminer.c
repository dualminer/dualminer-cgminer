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
#define CP210X_PREF_PACKET 256

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
#define DUALMINER_WAIT_TIMEOUT 400
#define DUALMINER_READ_TIMEOUT 100
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
//#define DUALMINER_SCRYPT_HASH_TIME		    0.00001428571429
#define DUALMINER_SCRYPT_HASH_TIME		    0.00001728571429
#define DUALMINER_SCRYPT_DM_HASH_TIME		0.00003333333333
#define DUALMINER_SHA2_HASH_TIME		    0.00000000300000
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
	int asics_count;
	bool keepwork;
	int matrix_m;
	int matrix_n;
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
	cg_rlock(&cgusb_fd_lock);
	if (libusb_control_transfer(dualminer->usbdev->handle, FTDI_TYPE_OUT, SIO_SET_MODEM_CTRL_REQUEST, usb_val, 0, NULL, 0, 200) < 0)
	{
		cg_runlock(&cgusb_fd_lock);
		return -1;
	}
	cg_runlock(&cgusb_fd_lock);
	return 0;
}

//mast after usb_init
static int dualminer_get_cts(struct cgpu_info *dualminer)
{
	char usb_val[2];
	unsigned short status;
	if(dualminer->usbdev == NULL)
	{
		return -1;
	}
	cg_rlock(&cgusb_fd_lock);
	if (libusb_control_transfer(dualminer->usbdev->handle, FTDI_TYPE_IN, SIO_POLL_MODEM_STATUS_REQUEST, 0, 1, (unsigned char *)usb_val, 2, 200) != 2)
	{
		cg_runlock(&cgusb_fd_lock);
		return -1;
	}
	cg_runlock(&cgusb_fd_lock);
	status = (usb_val[1] << 8) | (usb_val[0] & 0xFF);
	return ((status & 0x10) ? 0 : 1); 
}

static int dualminer_set_rts_status(struct cgpu_info *dualminer, unsigned int state)
{
	unsigned short usb_val;
	if(dualminer->usbdev == NULL)
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
	cg_rlock(&cgusb_fd_lock);
	if (libusb_control_transfer(dualminer->usbdev->handle, FTDI_TYPE_OUT, SIO_SET_MODEM_CTRL_REQUEST, usb_val, 2, NULL, 0, 200) < 0)
	{
		cg_runlock(&cgusb_fd_lock);
		return -1;
	}
	cg_runlock(&cgusb_fd_lock);
	return 0;	
}

static int dualminer_send_cmds(struct cgpu_info *dualminer, const char *cmds[], int interface)
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
	unsigned int data;

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
			{
			dualminer_send_cmds(dualminer,ltc_only_init,FTDI_INTERFACE_A);
			}
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
		case IDENT_CP:
                        usb_set_pps(dualminer, CP210X_PREF_PACKET); //
			//enable uart
                        transfer(dualminer, CP210X_TYPE_OUT, CP210X_REQUEST_IFC_ENABLE, CP210X_VALUE_UART_ENABLE,FTDI_INTERFACE_A, C_ENABLE_UART);
                        if (dualminer->usbinfo.nodev)
                                return;
                        // Set data control
                        transfer(dualminer, CP210X_TYPE_OUT, CP210X_REQUEST_DATA, CP210X_VALUE_DATA,FTDI_INTERFACE_A, C_SETDATA);
                        if (dualminer->usbinfo.nodev)
                                return;
			//set baud
                        data = CP210X_DATA_BAUD;
			_transfer(dualminer, CP210X_TYPE_OUT, CP210X_REQUEST_BAUD, 0,0, &data, sizeof(data), C_SETBAUD);
			
			if(!opt_dualminer_interface)
			{
				
                                _transfer(dualminer, CP210X_TYPE_OUT, CP210X_REQUEST_BAUD, 0,1, &data, sizeof(data), C_SETBAUD);
				dualminer_send_cmds(dualminer, btc_gating, FTDI_INTERFACE_A);
				dualminer_send_cmds(dualminer, btc_init, FTDI_INTERFACE_A);
				dualminer_send_cmds(dualminer, ltc_init, FTDI_INTERFACE_B);
			}
			else
			{
				dualminer_send_cmds(dualminer,ltc_only_init,FTDI_INTERFACE_A);
			}
				
			if(!opt_dualminer_interface)
			dualminer_send_cmds(dualminer, btc_open_nonce_unit, FTDI_INTERFACE_A);
			
			dualminer_send_cmds(dualminer, pll_freq_850M_cmd, FTDI_INTERFACE_A);
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

static void release_dualminer(struct cgpu_info *dualminer, int err)
{
	switch(err)
	{
		case LIBUSB_ERROR_IO:
		case LIBUSB_ERROR_OVERFLOW:
		case LIBUSB_ERROR_ACCESS:
		case LIBUSB_ERROR_BUSY:
		case LIBUSB_ERROR_NO_MEM:
		case LIBUSB_ERROR_TIMEOUT:
			dualminer_set_dtr(dualminer, 0);
			dualminer_set_rts_status(dualminer, RTS_LOW);
			cgsleep_ms(500);
			release_cgpu(dualminer);
			break;
		default:
			break;
	}
}
#define DM_NONCE_ERROR -1
#define DM_NONCE_OK 0
#define DM_NONCE_RESTART 1
#define DM_NONCE_TIMEOUT 2

static int dualminer_get_nonce(struct cgpu_info *dualminer, unsigned char *buf, struct timeval *tv_start, struct timeval *tv_finish, struct thr_info *thr, int read_time, bool is_ltc)
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

		err = usb_read_ii_once_timeout(dualminer, (opt_dualminer_interface ? 0 : (is_ltc ? 1 : 0)), (char *)buf,
					      DUALMINER_READ_SIZE, &amt, info->timeout, C_GETRESULTS);
		cgtime(&read_finish);
		if (err < 0 && err != LIBUSB_ERROR_TIMEOUT) {
			applog(LOG_ERR, "%s%i: Comms error (rerr=%d amt=%d)",
					dualminer->drv->name, dualminer->device_id, err, amt);
			dev_error(dualminer, REASON_DEV_COMMS_ERROR);
			release_dualminer(dualminer,err);
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

		if (read_time > DUALMINER_WAIT_TIMEOUT && info->timeout < DUALMINER_WAIT_TIMEOUT) {
				cgsleep_ms(DUALMINER_WAIT_TIMEOUT);
				if (thr && thr->work_restart) {
					applog(LOG_DEBUG, "dualminer Read: Work restart at %d ms", rc);
					return DM_NONCE_RESTART;
				}
		}
	}
}

static int dualminer_write(struct cgpu_info *dualminer, char *buf, int size, bool is_ltc)
{
	int err, amount;
	err = usb_write_ii(dualminer, (opt_dualminer_interface ? 0 : (is_ltc ? 1 : 0)), buf, size, &amount, C_SENDWORK);
	if(err != LIBUSB_SUCCESS || amount != size)
	{
		applog(LOG_ERR, "%s%i: Comms error (werr=%d amt=%d)", dualminer->drv->name, dualminer->device_id, err, amount);
		dev_error(dualminer, REASON_DEV_COMMS_ERROR);
//		libusb_reset_device(dualminer->usbdev->handle);
		dualminer->cgpu_err_accumulation++;
		if(dualminer->cgpu_err_accumulation>5)
			release_dualminer(dualminer, err);
		return 0;
	}
	if (opt_debug) 
	{
		applog(LOG_ERR, "\033[1;32m %s%i: Write to USB %s \033[0m", dualminer->drv->name, dualminer->device_id, bin2hex(buf, amount));
	}
	dualminer->cgpu_err_accumulation=0;
	return amount;
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
	case 5:
		nonce_mask = 0x3fffffff;
		break;
	case 8:
		nonce_mask = 0x1fffffff;
		break;
	default: break;
	}

	return nonce_mask;
}

static int dualminer_set_noce_range(struct cgpu_info *dualminer, bool is_ltc, int m, int n)
{
	int i, j;
	uint32_t nonce, step;
	unsigned char bin[12];
	char *p;
	if(!is_ltc)
	{
		step = 0xffffffff / n;
		for(i = 0; i < n; i++)
		{
			p = calloc(8, 1);
			if (unlikely(!p))
			{
				return -1;
			}
			memcpy(p, "\x55\xaa\x00\x00", 4);
			p[2] = i;
			nonce = htole32(step * i);
			memcpy(p + 4, &nonce, sizeof(nonce));
			applog(LOG_ERR, "\033[1;34m %s\033[0m", bin2hex(p, 8));
			dualminer_write(dualminer, p, 8, false);
			usleep(10*1000);
		}
	}
	else
	{
		for(j = 0; j < m; j++)
		{
			for(i = 0; i < n; i++)
			{
				memcpy(bin, "\x55\xaa\x10\x23\x00\x00\x00\x00\xff\xff\xff\x0f", 12);
				bin[2] = bin[2] + i;
				bin[7] = bin[7] + ((2*i)<<4);//(0x100 / (m * n))*(j * n + i);//0x00 + ((2*i)<<4);
				bin[11] = bin[11] + ((2*i+1)<<4);//(0x100 / (m * n)) * (j * n + i + 1) - 1; ////0x0f + ((2*i+1)<<4);
				dualminer_write(dualminer, (char *)bin, 12, true);
				usleep(2 * 1000);
			}
		}
	}
}

static int dualminer_detect_asics(struct cgpu_info *dualminer, bool is_ltc)
{
	int ok_count = 0;
	int i, amount, err, ret;
	char *nonce_hex;
	char *temp;
	unsigned char nonce_bin[DUALMINER_READ_SIZE];
	unsigned char ob_bin[160];
	struct timeval tv_start, tv_finish;
	for(i = 0; i < 0xf; i++)
	{
		if(is_ltc)
		{
			ltc_golden[5] = (i > 9 ? (0x61 + i - 10): (0x30 + i));
		}
		else
		{
			btc_golden[5] = (i > 9 ? (0x61 + i - 10) : (0x30 + i));
		}
		hex2bin(ob_bin, (is_ltc ? ltc_golden : btc_golden), sizeof(ob_bin));
		if(!dualminer_write(dualminer, ob_bin, (is_ltc ? 152 : 52), is_ltc))
		{
			continue;	
		}
		memset(nonce_bin, 0, sizeof(nonce_bin));
		usleep(1000);
		ret = dualminer_get_nonce(dualminer, nonce_bin, &tv_start, &tv_finish, NULL, 100, is_ltc);
		if (ret != DM_NONCE_OK)
			continue;
		rev(nonce_bin, 4);
	
		nonce_hex = bin2hex(nonce_bin, sizeof(nonce_bin));
		if (strncmp(nonce_hex, (is_ltc ? ltc_golden_nonce : btc_golden_nonce), 8) == 0)
		{
			ok_count++;
			applog(LOG_ERR, "\033[1;32mdualminer Detect %s: Test Success at %s: get %s, should: %s\033[0m", (is_ltc ? "LTC" : "BTC"), dualminer->device_path, nonce_hex, (is_ltc ? ltc_golden_nonce : btc_golden_nonce));
		}
		else
		{
			applog(LOG_ERR, "\033[1;31mDualMiner Detect %s: Test failed at %s: get %s, should: %s\033[0m", (is_ltc ? "LTC" : "BTC"), dualminer->device_path, nonce_hex,  (is_ltc ? ltc_golden_nonce : btc_golden_nonce));
		}
		free(nonce_hex);
		usleep(1000);
	}
	return ok_count;
}

static bool dualminer_detect_one(struct libusb_device *dev, struct usb_find_devices *found)
{
	int this_option_offset = ++option_offset;
	struct DUALMINER_INFO *info;
	struct timeval tv_start, tv_finish;

	int asics_count;
	int baud, tries;
	struct cgpu_info *dualminer;
	enum sub_ident ident;
	bool ok;
	baud = DUALMINER_IO_SPEED;
	dualminer = usb_alloc_cgpu(&dualminer_drv, 1);

	if (!usb_init(dualminer, dev, found))
		goto shin;
	usb_buffer_enable(dualminer);
	
	info = (struct DUALMINER_INFO *)calloc(1, sizeof(struct DUALMINER_INFO));
	if (unlikely(!info))
		quit(1, "Failed to malloc DUALMINER_INFO");
	dualminer->device_data = (void *)info;
	ident = usb_ident(dualminer);
	switch (ident) {
		case IDENT_DM:
		case IDENT_CP:
			info->timeout = DUALMINER_READ_TIMEOUT;
			info->keepwork = false;
			break;
		default:
			quit(1, "%s dualminer_detect_one() invalid %s ident=%d",
				dualminer->drv->dname, dualminer->drv->dname, ident);
	}

	dualminer_initialise(dualminer, baud);
	dualminer->cgpu_err_accumulation=0;
	tries = 1;
	ok = false;
	while (!ok && tries-- > 0) 
	{
		asics_count = dualminer_detect_asics(dualminer, (opt_scrypt ? true : false));
		if(asics_count >= 1)
		{
			ok = true;
			if(asics_count == 8 || asics_count == 5 || asics_count == 1)
			{
				info->keepwork = true;
			}
		}
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

	applog(LOG_DEBUG,"dualminer Detect: Test succeeded at %s: got %s", dualminer->device_path, btc_golden_nonce);

	/* We have a real dualminer! */
	if (!add_cgpu(dualminer))
		goto unshin;

	update_usb_stats(dualminer);

	applog(LOG_INFO, "%s%d: Found at %s",
		dualminer->drv->name, dualminer->device_id, dualminer->device_path);

	applog(LOG_DEBUG, "%s%d: Init baud=%d asics_count=%d",
	dualminer->drv->name, dualminer->device_id, baud, asics_count);

	info->baud = baud;
	info->asics_count = asics_count;
	info->nonce_mask = mask(asics_count);
	info->matrix_n = asics_count;
	info->matrix_m = 1;
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

static int dualmine_send_task(struct cgpu_info *dualminer, struct work *work, bool is_ltc)
{
	struct DUALMINER_INFO *info;
	unsigned char ob_bin[64], btc_bin[52], ltc_bin[160];
	info = (struct DUALMINER_INFO *)dualminer->device_data;
	if(is_ltc)
	{
		if(!opt_dualminer_interface)
		{
        	dualminer_send_cmds(dualminer, ltc_init, 1);
		}
		else
		{
			dualminer_send_cmds(dualminer, ltc_restart, 0);
			usleep(10 * 1000);
		}
		if(info->matrix_n == 1)
		{
			memset(ltc_bin, 0, sizeof(ltc_bin));
			memcpy(ltc_bin, "\x55\xaa\x1f\x00", 4);
			memcpy(ltc_bin + 4, work->target, 32);
			memcpy(ltc_bin + 36, work->midstate, 32);
			memcpy(ltc_bin + 68, work->data, 80);
			memcpy(ltc_bin + 148, "\xff\xff\xff\xff", 4);
			dualminer_write(dualminer, (char *)(ltc_bin), 152, true);
			usleep(10 * 1000);
		}
		else if(info->matrix_n > 1)
		{
			memset(ltc_bin, 0, sizeof(ltc_bin));
			memcpy(ltc_bin, "\x55\xaa\x1f\x00", 4);
			memcpy(ltc_bin + 4, work->target, 32);
			memcpy(ltc_bin + 36, work->midstate, 32);
			dualminer_write(dualminer, (char *)(ltc_bin), 152 - 8 - 76, true);   	
			usleep(10 * 1000);
			memset(ltc_bin, 0, sizeof(ltc_bin));
			memcpy(ltc_bin, "\x55\xaa\x1f\x10", 4);
			memcpy(ltc_bin + 4, work->data, 76);
			dualminer_write(dualminer, (char *)(ltc_bin), 152 - 8 - 64, true);
			usleep(10 * 1000);
			dualminer_set_noce_range(dualminer, true, info->matrix_m, info->matrix_n);
		}
		else
		{
		}
	}
	else
	{
		memset(ob_bin, 0, sizeof(ob_bin));
		memcpy(ob_bin, work->midstate, 32);
		memcpy(ob_bin + 52, work->data + 64, 12);
		memset(btc_bin, 0, sizeof(btc_bin));
		memcpy(btc_bin, "\x55\xaa\x1f\x00", 4);
		memcpy(btc_bin + 8, ob_bin, 32);
		memcpy(btc_bin + 40, ob_bin + 52, 12);
	}
}
static int64_t dualminer_scanhash(struct thr_info *thr, struct work *work,
				__maybe_unused int64_t max_nonce)
{
	struct cgpu_info *dualminer = thr->cgpu;
	struct DUALMINER_INFO *info = (struct DUALMINER_INFO *)(dualminer->device_data);
	int ret, err, amount;
	unsigned char nonce_bin[DUALMINER_READ_SIZE];
	char *ob_hex;
	uint32_t nonce;
	int64_t hash_count, hash_count_done = 0;
	struct timeval tv_start, tv_finish, elapsed;
	struct timeval tv_history_start, tv_history_finish;
	struct timeval loop_start, loop_finish, loop_elapsed;
	struct timeval diff, diff_start, diff_finish;
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
	
//	info->matrix_m = total_devices;	
	// Device is gone
	if (dualminer->usbinfo.nodev)
		return -1;

	if (!info->initialised)
		dualminer_initialise(dualminer, info->baud);

	elapsed.tv_sec = elapsed.tv_usec = 0;
	dualmine_send_task(dualminer, work, opt_scrypt);
	/* dualminer will return 4 bytes (DUALMINER_READ_SIZE) nonces or nothing */
	if (opt_debug)
	{
		applog(LOG_ERR, "\033[1;36m ==> %s%d: loop_elapsed.tv_sec = %d, thr = %x, !thr->work_restart = %x, info->keepwork = %x  <==\033[0m",
        		dualminer->drv->name, dualminer->device_id, loop_elapsed.tv_sec, thr, !thr->work_restart, info->keepwork);
	}
	cgtime(&loop_start);
	cgtime(&diff_start);
	do
	{
	/* dualminer will return 4 bytes (DUALMINER_READ_SIZE) nonces or nothing */
		memset(nonce_bin, 0, sizeof(nonce_bin));
		ret = dualminer_get_nonce(dualminer, nonce_bin, &tv_start, &tv_finish, thr, (opt_scrypt ? 5000: 1600), opt_scrypt);
		if (ret == DM_NONCE_ERROR)
			return 0;
		rev(nonce_bin, 4);
		work->blk.nonce = 0xffffffff;

		timersub(&tv_finish, &tv_start, &elapsed);

		// aborted before becoming idle, get new work
		if (ret == DM_NONCE_TIMEOUT || ret == DM_NONCE_RESTART) {
		
			// ONLY up to just when it aborted
			// We didn't read a reply so we don't subtract DUALMINER_READ_TIME
			estimate_hashes = ((double)(elapsed.tv_sec) + ((double)(elapsed.tv_usec)) / ((double)1000000)) / DUALMINER_SCRYPT_HASH_TIME; 
			// If some Serial-USB delay allowed the full nonce range to
			// complete it can't have done more than a full nonce
			if (unlikely(estimate_hashes > 0xffffffff))
				estimate_hashes = 0xffffffff;

			applog(LOG_DEBUG, "%s%d: no nonce = 0x%08lX hashes (%ld.%06lds)",
				dualminer->drv->name, dualminer->device_id,
				(long unsigned int)estimate_hashes,
				elapsed.tv_sec, elapsed.tv_usec);
			hash_count_done += estimate_hashes;
			goto oversubmit;
		}

		memcpy((char *)&nonce, nonce_bin, sizeof(nonce_bin));
		nonce = htobe32(nonce);
		curr_hw_errors = dualminer->hw_errors;
		submit_nonce(thr, work, nonce);
		was_hw_error = (curr_hw_errors < dualminer->hw_errors);
		if (!was_hw_error)
		{
			//do_dualminer_close(thr);
			hash_count = opt_scrypt ? nonce & info->nonce_mask : ((double)(((double)nonce)*opt_btc_number)/160);
//			info->golden_hashes=(double)hash_count/((double)(elapsed.tv_sec) + ((double)(elapsed.tv_usec))/((double)1000000));	
			applog(LOG_DEBUG, "dualminer hashcount = %d, hashrate=%d, opt_btc_number=%d", hash_count, info->golden_hashes, opt_btc_number);
		
		}
		else
		{
			hash_count = ((double)(elapsed.tv_sec) + ((double)(elapsed.tv_usec))/((double)1000000)) / DUALMINER_SCRYPT_HASH_TIME;
		}
		hash_count *= info->asics_count;
		hash_count_done += hash_count;
oversubmit:
		cgtime(&diff_finish);
		timersub(&diff_finish, &diff_start, &diff);
		if ((hash_count && (diff.tv_sec > 0 || diff.tv_usec > 200000 || diff.tv_sec >= opt_log_interval))) 
		{
			hashmeter(thr->id, &diff, hash_count_done);
			hash_count_done = 0;
			diff.tv_sec = 0;
			diff.tv_usec = 0;
			cgtime(&diff_start);
		}

		cgtime(&loop_finish);
		timersub(&loop_finish, &loop_start, &loop_elapsed);
	}
	while((thr && !thr->work_restart) && info->keepwork && loop_elapsed.tv_sec < 60);
	if (opt_debug)
	{
		applog(LOG_ERR, "\033[1;34m ==> %s%d: loop_elapsed.tv_sec = %d, thr = %x, !thr->work_restart = %x, info->keepwork = %x  <==\033[0m",
                        dualminer->drv->name, dualminer->device_id, loop_elapsed.tv_sec, thr, !thr->work_restart, info->keepwork);
	}
	return 0;
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
