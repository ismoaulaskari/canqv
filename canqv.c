/*
 * Copyright 2015 Kurt Van Dijck <dev.kurt@vandijck-laurijssen.be>
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>
#include <math.h>
#include <sys/time.h>

#include <error.h>
#include <getopt.h>
#include <sys/socket.h>
#include <linux/can.h>
#include <linux/can/raw.h>
#include <net/if.h>

/* terminal codes, copied from can-utils */

#define CLR_SCREEN  "\33[2J"
#define CSR_HOME  "\33[H"
#define ATTRESET "\33[0m"

#define NAME "canqv"

/* program options */
static const char help_msg[] =
        NAME ": CAN spy\n"
        "usage:	" NAME " [OPTIONS ...] DEVICE ID[/MASK] ...\n"
        "\n"
        "Options\n"
        " -V, --version		Show version\n"
        " -v, --verbose		Verbose output\n"
        "\n"
        " -m, --maxperiod=TIME	Consider TIME as maximum period (default 2s).\n"
        "			Slower rates are considered multiple one-time ID's\n"
        " -x, --remove=TIME	Remove ID's after TIME (default 10s).\n"
        "\n"
        ;
#ifdef _GNU_SOURCE
static struct option long_opts[] = {
    { "help", no_argument, NULL, '?',},
    { "version", no_argument, NULL, 'V',},
    { "verbose", no_argument, NULL, 'v',},

    { "remove", required_argument, NULL, 'x',},
    { "maxperiod", required_argument, NULL, 'm',},
    {},
};
#else
#define getopt_long(argc, argv, optstring, longopts, longindex) \
        getopt((argc), (argv), (optstring))
#endif
static const char optstring[] = "V?vx:m:";
static int verbose;
static double deadtime = 10.0;
static double maxperiod = 2.0;

/* jiffies, in msec */
static double jiffies;

static void update_jiffies(void) {
    struct timeval tv;

    gettimeofday(&tv, NULL);
    jiffies = tv.tv_sec + tv.tv_usec / 1e6;
}

/* cache definition */
struct cache {
    struct can_frame cf;
    int flags;
#define F_DIRTY  0x01
    double lastrx;
    double period;
};

static int cmpcache(const void *va, const void *vb) {
    const struct cache *a = va, *b = vb;

    return a->cf.can_id - b->cf.can_id;
}

static int isCommand(int id) {
    if (id >= 0xC0 && id < 0xD0) {
        return 1;
    }
    return 1;
}

static char *unitName(int id) {
    if (0x1b == id) return "MUM"; //dummy test unitname
    if (0x40 == id) return "CEM"; //low speed can
    if (0x51 == id) return "DIM";
    if (0x48 == id) return "SWM";
    if (0x29 == id) return "CCM";
    if (0x43 == id) return "DDM";
    if (0x45 == id) return "PDM";
    if (0x2e == id) return "PSM";
    if (0x46 == id) return "REM";
    if (0x58 == id) return "SRS";
    if (0x47 == id) return "UEM";
    if (0x60 == id) return "AUM";
    if (0x64 == id) return "PHM";
    if (0x50 == id) return "CEH"; //high-speed can units with H-ending:
    if (0x01 == id) return "BCH";
    if (0x52 == id) return "AEM";
    if (0x11 == id) return "ECH";
    if (0x28 == id) return "SAH"; //SAS
    if (0x6e == id) return "TCH";
    if (0x62 == id) return "RTI";
    return "";
}

void appendLog(FILE *fp, struct can_frame cf) {
    fp = fopen("/tmp/canqv_captures.log", "a");
    unsigned char *row = cf.data;
    //fputs(row, fp);
    fprintf(fp, "%08x:  %02x  %03s  %02x  %02x  %02x  %02x  %02x  %02x  %02x \n", cf.can_id & CAN_EFF_MASK, row[0],unitName(row[1]),row[2],row[3],row[4],row[5],row[6],row[7],row[8]);
    fclose(fp);
}

int main(int argc, char *argv[]) {
    int opt, ret, sock, row, byte;
    const char *device;
    char *endp;
    struct can_filter *filters;
    size_t nfilters, sfilters;
    struct sockaddr_can addr = {.can_family = AF_CAN,};
    struct cache *cache, w, *curr;
    size_t ncache, scache;
    double last_update, lastseen;
    FILE *fp;

    /* argument parsing */
    while ((opt = getopt_long(argc, argv, optstring, long_opts, NULL)) != -1)
        switch (opt) {
            case 'V':
                fprintf(stderr, "%s %s, "
                        "Compiled on %s %s\n",
                        NAME, VERSION, __DATE__, __TIME__);
                exit(0);
                break;
            default:
                fprintf(stderr, "%s: unknown option '%u'\n\n", NAME, opt);
            case '?':
                fputs(help_msg, stderr);
                return opt != '?';
            case 'v':
                ++verbose;
                break;
            case 'x':
                deadtime = strtod(optarg, NULL);
                break;
            case 'm':
                maxperiod = strtod(optarg, NULL);
                break;
        }

    /* parse CAN device */
    if (argv[optind]) {
        addr.can_ifindex = if_nametoindex(argv[optind]);
        if (!addr.can_ifindex)
            error(1, errno, "device '%s' not found", argv[optind]);
        device = argv[optind];
        ++optind;
    } else
        device = "any";

    /* parse filters */
    filters = NULL;
    sfilters = nfilters = 0;
    for (; optind < argc; ++optind) {
        if (nfilters >= sfilters) {
            sfilters += 16;
            filters = realloc(filters, sizeof (*filters) * sfilters);
            if (!filters)
                error(1, errno, "realloc");
        }
        filters[nfilters].can_id = strtoul(argv[optind], &endp, 16);
        if ((endp - argv[optind]) > 3)
            filters[nfilters].can_id |= CAN_EFF_MASK;
        if (strchr(":/", *endp))
            filters[nfilters].can_mask = strtoul(endp + 1, NULL, 16) |
            CAN_EFF_FLAG | CAN_RTR_FLAG;
        else
            filters[nfilters].can_mask = CAN_EFF_MASK |
                CAN_EFF_FLAG | CAN_RTR_FLAG;
        ++nfilters;
    }

    /* prepare socket */
    sock = ret = socket(PF_CAN, SOCK_RAW, CAN_RAW);
    if (ret < 0)
        error(1, errno, "socket PF_CAN");

    if (nfilters) {
        ret = setsockopt(sock, SOL_CAN_RAW, CAN_RAW_FILTER, filters,
                nfilters * sizeof (*filters));
        if (ret < 0)
            error(1, errno, "setsockopt %li filters", nfilters);
    }

    ret = bind(sock, (struct sockaddr *) &addr, sizeof (addr));
    if (ret < 0)
        error(1, errno, "bind %s", device);

    /* pre-init cache */
    scache = ncache = 0;
    cache = NULL;

    last_update = 0;
    while (1) {
        ret = recv(sock, &w.cf, sizeof (w.cf), 0);
        if (ret < 0)
            error(1, errno, "recv %s", device);
        if (!ret)
            break;

        update_jiffies();
        curr = bsearch(&w, cache, ncache, sizeof (*cache), cmpcache);
        if (!curr && (ncache >= scache)) {
            /* grow cache */
            scache += 16;
            cache = realloc(cache, sizeof (*cache) * scache);
            memset(cache + ncache, 0, (scache - ncache) * sizeof (*cache));
        }
        if (!curr) {
            /* add in cache */
            curr = cache + ncache++;
            curr->flags |= F_DIRTY;
            curr->cf = w.cf;
            curr->period = NAN;
            curr->lastrx = jiffies;
            qsort(cache, ncache, sizeof (*cache), cmpcache);
        } else {
            if ((curr->cf.can_id != w.cf.can_id) ||
                    (curr->cf.can_dlc != w.cf.can_dlc) ||
                    memcmp(curr->cf.data, w.cf.data, w.cf.can_dlc))
                curr->flags |= F_DIRTY;
            /* update cache */
            curr->cf = w.cf;
            curr->period = jiffies - curr->lastrx;
            if (curr->period > maxperiod)
                curr->period = NAN;
            curr->lastrx = jiffies;
        }

        if ((jiffies - last_update) < 0.25)
            continue;
        /* remove dead cache */
        for (row = 0; row < ncache; ++row) {
            curr = cache + row;
            lastseen = jiffies - curr->lastrx;

            if (lastseen > deadtime) {
                /* delete this entry */
                memcpy(cache + row, cache + row + 1, (ncache - row - 1) * sizeof (*cache));
                --ncache;
                --row;
                continue;
            }

            if (!isnan(curr->period) && (lastseen > 2 * curr->period))
                /* reset period */
                curr->period = NAN;
        }

        last_update = jiffies;
        /* update screen */
        puts(CLR_SCREEN ATTRESET CSR_HOME);

        puts("          .----------------------- Message length");
        puts("          |  .-------------------- Module id (list below)");
        puts("          |  |  .----------------- Read Data Block By Offset");
        puts("          |  |  |  .---- Identify (?)");
        puts("          |  |  |  |");
        puts("          |  |  |  |");
        puts("000FFFFE CB xx B9 F0 00 00 00 00");
        puts("00 0F FF FE: The identifier VIDA (or any other diagnostic module) uses for messaging.");
        puts("Message length: High nibble seems to be always 'C' in command message. Low nibble: Bit 3 is always on. Bits 0-2 is the actual message length (excluding the first byte).");
        puts("");
        
        for (row = 0; row < ncache; ++row) {
            int command_flag = 0;
            if (cache[row].cf.can_id & CAN_EFF_FLAG)
                printf("%08x:", cache[row].cf.can_id & CAN_EFF_MASK);
            else
                printf("     %03x:", cache[row].cf.can_id & CAN_SFF_MASK);
            for (byte = 0; byte < cache[row].cf.can_dlc; ++byte) {
                if (byte == 0) {
                    if (isCommand(cache[row].cf.data[byte]) == 1) command_flag = 1;
                }
                if (byte == 1) {
                    char unit[3];
                    strcpy(unit, unitName(cache[row].cf.data[byte]));
                    if (strlen(unit) > 2 && command_flag == 1) {
                        printf(" %3s ", unit);
                        appendLog(fp, cache[row].cf);
                    } else {
                        printf(" %02x  ", cache[row].cf.data[byte]);
                    }
                } else {
                    //printf(" %3s ", "TST");
                    printf(" %02x  ", cache[row].cf.data[byte]);
                }        
            }
            for (; byte < 8; ++byte)
                printf(" --");
            printf("\tlast=-%.3lfs", jiffies - cache[row].lastrx);
            if (!isnan(cache[row].period))
                printf("\tperiod=%.3lfs", cache[row].period);
            printf("\n");
            cache[row].flags &= F_DIRTY;
        }

        puts("");
        puts("00 80 00 03 :: 40  CEM, Central Electronic Module");
        puts("                   (also answers queries related to CPM(heater)");
        puts("00 80 00 09 :: 51  DIM, Driver Information Module");
        puts("00 80 08 01 :: 48  SWM, Steering Wheel Module");
        puts("00 80 10 01 :: 29  CCM, Climate Control Module");
        puts("00 80 00 11 :: 43  DDM, Driver Door Module");
        puts("00 80 00 81 :: 45  PDM, Passenger Door Module");
        puts("00 80 01 01 :: 2e  PSM, Power Seat Module");
        puts("00 80 04 01 :: 46  REM, Rear Electronic Module");
        puts("00 80 02 01 :: 58  SRS, Air bag");
        puts("00 80 20 01 :: 47  UEM, Upper Electronic Module");
        puts("00 80 00 05 :: 60  AUM, Audio Module");
        puts("00 80 00 21 :: 64  PHM, Phone Module");
        puts("");
/*
        puts("50  CEM, Central Electronic Module (Hi-speed interface)");
        puts("01  BCM, Break Control Module (hi-speed network)");
        puts("52  AEM, Accessory Electronic Module");
        puts("11  ECM, Engine Control Module (hi-speed network)");
        puts("28  SAS, Steering Angle Sensor (hi-speed network)");
        puts("6e  TCM, Transmission Control Module (hi-speed network)");
        puts("62  RTI, Road Traffic Information module");
*/

    }
    return 0;
}

