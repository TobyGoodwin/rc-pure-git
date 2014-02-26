#include "parse.h"
/*
vim: syntax=c
*/

#if PACC_ASSERT
#undef NDEBUG
#else
#define NDEBUG 1
#endif
#define PACC_XGLUE(a, b) a ## _ ## b
#define PACC_GLUE(a, b) PACC_XGLUE(a, b)
#define PACC_SYM(s) PACC_GLUE(PACC_NAME, s)
#define PACC_TRACE if (PACC_CAN_TRACE && PACC_SYM(trace))

#include <assert.h>
#include <ctype.h>
#include <stdarg.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

int PACC_SYM(trace) = 0;

static void pacc_panic(const char *e) {
    fprintf(stderr, "pacc: panic: %s\n", e);
    exit(1);
}

static void pacc_nomem(void) { pacc_panic("out of memory"); }

enum pacc_status {
    no_parse, parsed, evaluated, uncomputed
};

typedef size_t *ref_t;


/* note that this actually needs to appear before any system header
   files are included; byacc likes to throw in <stdlib.h> first. */
#include "rc.h"

static Node *star, *nolist;
Node *parsetree;	/* not using yylval because bison declares it as an auto */

    static const int n_rules = 48;
    static const int start_rule_id = 124;
    union PACC_SYM(vals) {
      Node * u0;
      redirtype u1;
      int u2;
      struct Node * u3;
      ref_t u4;
    }
    ;
#define TYPE_PRINTF "%p"
#define PACC_TYPE Node *

struct pacc_mid {
    /* Where in the matrix are we? Note that the bottom two bits of rule
     * also encode a status. */
    long rule; size_t col;
    size_t remainder; /* unparsed string */
    long expr_id; /* id of the expression to evaluate, yielding... */
    union PACC_SYM(vals) value; /* ... the semantic value */
    struct {
	long call_id; /* a call */
	size_t col; /* a column */
    } *evlis;
    size_t ev_alloc;
    size_t ev_valid;
};

static struct pacc_mid *cur;

static void _pacc_save_core(long c, size_t col) {
    PACC_TRACE fprintf(stderr, "_pacc_save_core(%ld, %ld)\n", c, col);
    if (cur->ev_valid == cur->ev_alloc) {
	cur->ev_alloc = cur->ev_alloc * 2 + 1;
	cur->evlis = realloc(cur->evlis, cur->ev_alloc * sizeof(*cur->evlis));
	if (!cur->evlis) pacc_nomem();
    }
    cur->evlis[cur->ev_valid].call_id = c;
    cur->evlis[cur->ev_valid].col = col;
    ++cur->ev_valid;
}

struct _pacc_coord {
    size_t n;
    int c[2];
};

/* a pacc parser */
struct pacc_parser {
    unsigned char *string;
    size_t input_length;
    PACC_TYPE value;
    struct pacc_mid **m_bkt;
    unsigned int m_bkt_cnt;
    unsigned char *m_valid;
    unsigned char m_chain_max;
    
    unsigned char *stack; /* the stack */
    unsigned char *sp; /* next slot in stack */
    unsigned char *stack_alloc; /* last slot in stack */

    /* Dynamic array of error strings */
    char **err;
    size_t err_alloc;
    size_t err_valid;
    /* The highest column to have associated error */
    size_t err_col;

    /* Dynamic array of co-ordinates */
    struct _pacc_coord *coord;
    size_t coord_alloc;
    size_t coord_valid;
};

static void _pacc_push(void *x, size_t s, struct pacc_parser *p) {
    if (p->sp + s >= p->stack_alloc) {
	size_t l = 2 * (p->stack_alloc - p->stack) + s;
	unsigned char *n = realloc(p->stack, l);
	if (!n) pacc_nomem();
	p->sp = n + (p->sp - p->stack);
	p->stack = n;
	p->stack_alloc = n + l + 1;
    }
    assert(p->sp >= p->stack && p->sp + s < p->stack_alloc);
    memcpy(p->sp, x, s);
    p->sp += s;
}

#define _pacc_Push(v) _pacc_push(&(v), sizeof (v), _pacc)

static void *_pacc_pop(size_t s, struct pacc_parser *p) {
    assert(p->sp - s >= p->stack);
    p->sp -= s;
    return p->sp;
}

#define _pacc_Pop(v) memcpy(&(v), _pacc_pop(sizeof (v), _pacc), sizeof (v))
#define _pacc_Discard(v) ((void)_pacc_pop(sizeof (v), _pacc))

#define ref() (&cur->col)
#define ref_0(a) (_pacc->string[*a])
#define ref_cmp(a, s) (_pacc_ref_cmp((a), (s), _pacc))
#define ref_dup(a) (_pacc_ref_dup((a), _pacc))
#define ref_len(a) ((a)[1] - (a)[0])
#define ref_ptr(a) (_pacc->string + *(a))
#define ref_str() (_pacc_ref_dup(ref(), _pacc))
#define ref_streq(a, b) (_pacc_ref_streq((a), (b), _pacc))

static char *_pacc_ref_dup(ref_t a, struct pacc_parser *p) {
    char *restrict r;
    const char *restrict s;
    size_t l;

    l = a[1] - a[0];
    r = realloc(0, l + 1); if (!r) pacc_nomem();
    s = (char *)p->string + a[0];
    strncpy(r, s, l);
    r[l] = '\0';
    return r;
}


// Copyright (c) 2008-2010 Bjoern Hoehrmann <bjoern@hoehrmann.de>
// See http://bjoern.hoehrmann.de/utf-8/decoder/dfa/ for details.

#define PACC_UTF8_ACCEPT 0
#define PACC_UTF8_REJECT 12

static const uint8_t utf8d[] = {
  // The first part of the table maps bytes to character classes that
  // to reduce the size of the transition table and create bitmasks.
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,  9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,
   7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,  7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,
   8,8,2,2,2,2,2,2,2,2,2,2,2,2,2,2,  2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,
  10,3,3,3,3,3,3,3,3,3,3,3,3,4,3,3, 11,6,6,6,5,8,8,8,8,8,8,8,8,8,8,8,

  // The second part is a transition table that maps a combination
  // of a state of the automaton and a character class to a state.
   0,12,24,36,60,96,84,12,12,12,48,72, 12,12,12,12,12,12,12,12,12,12,12,12,
  12, 0,12,12,12,12,12, 0,12, 0,12,12, 12,24,12,12,12,12,12,24,12,24,12,12,
  12,12,12,12,12,12,12,24,12,12,12,12, 12,24,12,12,12,12,12,12,12,24,12,12,
  12,12,12,12,12,12,12,36,12,36,12,12, 12,36,12,12,12,12,12,36,12,36,12,12,
  12,36,12,12,12,12,12,12,12,12,12,12, 
};

inline static uint32_t
pacc_decode(uint32_t* state, uint32_t* codep, uint32_t byte) {
  uint32_t type = utf8d[byte];

  *codep = (*state != PACC_UTF8_ACCEPT) ?
    (byte & 0x3fu) | (*codep << 6) :
    (0xff >> type) & (byte);

  *state = utf8d[256 + *state + type];
  return *state;
}

/*

License

Copyright (c) 2008-2009 Bjoern Hoehrmann <bjoern@hoehrmann.de>

Permission is hereby granted, free of charge, to any person obtaining a
copy of this software and associated documentation files (the
"Software"), to deal in the Software without restriction, including
without limitation the rights to use, copy, modify, merge, publish,
distribute, sublicense, and/or sell copies of the Software, and to
permit persons to whom the Software is furnished to do so, subject to
the following conditions:

The above copyright notice and this permission notice shall be included
in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS
OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

*/

/* _pacc_utf8_char attempts to read a single UTF8 encoded character from
 * the string p with length m. Its return value is the number of bytes
 * in the character, 0 in case of error; *c holds the character read. */
static int _pacc_utf8_char(unsigned char *p, int m, uint32_t *c) {
    uint32_t state = PACC_UTF8_ACCEPT;
    int i = 0;
    do
	if (state == PACC_UTF8_REJECT || i == m) return 0;
    while (pacc_decode(&state, c, p[i++]));
    return i;
}

static int _pacc_ref_streq(ref_t a, char *b, struct pacc_parser *p) {
    /* XXX this could be made quicker */
    if (strlen(b) != (size_t)(a[1] - a[0])) return 0;
    return strncmp((const char *)p->string + a[0], b, a[1] - a[0]) == 0; 
}

/* Find the largest available prime which is smaller than the target
 * bucket count. This exponential selection of primes was generated by
 * Dan Bernstein's primegen-0.97 package, using the following:

perl -le '$x=1;while(($e=int(exp($x/1)))<2**32){print "./primes ",$e," ",100+$e," | sed 1q";++$x}' | sh

 * except that I replaced 2 with 3.
 */
static void _pacc_set_bkt_cnt(struct pacc_parser *p) {
    static unsigned int primes[] = {
	3, 7, 23, 59, 149, 409, 1097, 2999, 8111, 22027, 59879, 162779, 442439,
	1202609, 3269029, 8886113, 24154957, 65659969, 178482319, 485165237,
	1318815761, 3584912873U
    };
    int i, p_sz = sizeof(primes) / sizeof(*primes);
    unsigned long bkt_cnt = n_rules * (p->input_length + 1) / 100;

    for (i = 1; i < p_sz; ++i) {
	if (primes[i] > bkt_cnt) break;
    }
    p->m_bkt_cnt = primes[i - 1];
}

struct pacc_parser *PACC_SYM(new)(void) {
    struct pacc_parser *p;

    p = realloc(0, sizeof *p);
    if (!p) pacc_nomem();
    p->m_chain_max = 0;
    p->sp = 0;
    p->stack = p->stack_alloc = 0;
    p->err = 0;
    p->err_alloc = p->err_valid = 0;
    p->coord = 0;
    p->coord_alloc = p->coord_valid = 0;
    return p;
}

void PACC_SYM(input)(struct pacc_parser *p, char *s, size_t l) {
    unsigned int i;

    p->string = (unsigned char *)s;
    p->input_length = l;
    _pacc_set_bkt_cnt(p);
    p->m_bkt = realloc(0, sizeof(struct pacc_mid *) * p->m_bkt_cnt);
    if (!p->m_bkt) pacc_nomem();
    p->m_valid = realloc(0, 2 * p->m_bkt_cnt);
    for (i = 0; i < p->m_bkt_cnt; ++i) {
	p->m_bkt[i] = 0;
	p->m_valid[i * 2] = 0; /* valid */
	p->m_valid[i * 2 + 1] = 0; /* allocated */
    }
}

void PACC_SYM(destroy)(struct pacc_parser *p) {
    free(p->m_bkt);
    free(p->m_valid);
    free(p);
}

/* hash chains */
static struct pacc_mid *_pacc_result(struct pacc_parser *p, size_t col, long rule) {
    unsigned char i;
    unsigned int h;
    struct pacc_mid *bkt, *r;

    assert(col < p->input_length + 1);
    PACC_TRACE fprintf(stderr, "_pacc_result(%ld, %ld)\n", col, rule);
    h = (col + (rule << 6) + (rule << 16) - rule) % p->m_bkt_cnt;
    bkt = p->m_bkt[h];
    for (i = 0; i < p->m_valid[h * 2]; ++i) {
	r = bkt + i;
	if (r->col == col && r->rule >> 4 == rule)
	    return r;
    }
    if (i == p->m_valid[h * 2 + 1]) {
	if (i == 255) pacc_panic("bucket too large");
	if (i + 1 > p->m_chain_max) p->m_chain_max = i + 1;
	p->m_bkt[h] = bkt = realloc(bkt, p->m_chain_max * sizeof(struct pacc_mid));
	if (!bkt) pacc_nomem();
	p->m_valid[h * 2 + 1] = p->m_chain_max;
    }
    r = bkt + i;
    /* Initialize the new element. */
    r->col = col; r->rule = rule << 4 | uncomputed;
    r->evlis = 0;
    r->ev_alloc = r->ev_valid = 0;
    /* Correct use of a side effect in an (unfailing) assert. */
    assert((r->expr_id = 0) == 0);
    ++(p->m_valid[h * 2]);
    return r;
}

static int _pacc_error(struct pacc_parser *_pacc, char *what, size_t col) {
    int doit, append;

    PACC_TRACE fprintf(stderr, "_pacc_error(%s, %ld)\n", what, col);
    append = doit = 1;
    if (col > _pacc->err_col) append = 0;
    else if (col == _pacc->err_col) {
        size_t i;
        for (i = 0; i < _pacc->err_valid; ++i) {
            if (strcmp(_pacc->err[i], what) == 0) doit = 0;
        }
    } else doit = 0;
    if (doit) {
        if (append) ++_pacc->err_valid;
        else _pacc->err_valid = 1;
        if (_pacc->err_valid > _pacc->err_alloc) {
            _pacc->err_alloc = 2 * _pacc->err_alloc + 1;
            _pacc->err = realloc(_pacc->err, _pacc->err_alloc * sizeof(char *));
            if (!_pacc->err) pacc_nomem();
        }
        _pacc->err[_pacc->err_valid - 1] = what;
        _pacc->err_col = col;
    }
    return 0; /* for the fail() macro */
}

/* Given a parser p, and a column col, return the "coordinates" in a
 * pair of ints: coord[0] is the line number, and coord[1] is the column
 * within the line, both 1-based. */
static int *_pacc_coords(struct pacc_parser *p, size_t col) {
    unsigned int i;
    int x, y, hi, lo;
    struct _pacc_coord *c, *cs = p->coord;

    /* binary search */
    lo = 0; hi = p->coord_valid;
    while (lo < hi) {
	int mid = (lo + hi) / 2;
	if (cs[mid].n < col) lo = mid + 1;
	else if (cs[mid].n > col) hi = mid;
	else return cs[mid].c;
    }

    /* increase list if necessary */
    if (p->coord_valid + 1 > p->coord_alloc) {
    	struct _pacc_coord *n;
	p->coord_alloc = p->coord_alloc * 2 + 1;
	n = realloc(p->coord, p->coord_alloc * sizeof *n);
	if (!n) pacc_nomem();
	cs = p->coord = n;
    }

    /* move hole to the right place */
    memmove(cs + lo + 1, cs + lo, (p->coord_valid - lo) * sizeof *cs);
    ++p->coord_valid;

    /* find the coordinates */
    c = cs + lo; c->n = col;
    if (lo > 0) { y = cs[lo - 1].c[0]; i = cs[lo - 1].n; }
    else { y = 1; /* line numbering is 1-based, natch */ i = 0; }
    x = 1;
    while (i < col) {
	uint32_t c;
	int l = _pacc_utf8_char(p->string + i, p->input_length - i, &c);
	if (!l) pacc_panic("invalid UTF-8 input");
	i += l;
	++x;
	if (c == '\n') { ++y; x = 1; }
    }

    /* memoize them */
    c->c[0] = y;
    /* column numbering is also 1-based; start points to \n */
    c->c[1] = x;
    return c->c;
}
/* The userland version */
#define pacc_coords _pacc_coords(_pacc, _x)

static void pacc_pr(char **buf, size_t *l, char *fmt, ...) {
    size_t n;
    va_list argp;

    va_start(argp, fmt);
    n = vsnprintf(0, 0, fmt, argp);
    va_end(argp);

    *buf = realloc(*buf, *l + n + 1);
    if (!buf) pacc_nomem();

    va_start(argp, fmt);
    vsnprintf(*buf + *l, n + 1, fmt, argp);
    va_end(argp);
    *l += n;
}

char *PACC_SYM(pos)(struct pacc_parser *p, const char *s) {
    int *coords;
    size_t l = 0;
    char *r = 0;

    coords = _pacc_coords(p, p->err_col);
    pacc_pr(&r, &l, "%d:%d: %s", coords[0], coords[1], s);

    return r;
}

char *PACC_SYM(error)(struct pacc_parser *p) {
    size_t i, l = 0;
    char *r = 0;

    /* XXX this, or something like it, is very handy, and needs to go
     * in. But we're holding off for now as all failing test cases would
     * need to be changed. */
    //printf("got `%c', ", p->string[p->err_col]); /* XXX UTF-8? */

    if (p->err_valid && p->err[0][0] == '.')
	pacc_pr(&r, &l, "expected ");
    for (i = 0; i < p->err_valid; ++i) {
	char *s = p->err[i];
	if (*s == '.') ++s;
	for ( ; *s; ++s) {
	    if (isprint(*s)) pacc_pr(&r, &l, "%c", *s);
	    else switch (*s) {
		case '\n':
		    pacc_pr(&r, &l, "\\n");
		    break;
		default:
		    pacc_pr(&r, &l, "\\x%02x", *s);
		    break;
	    }
	}

	if (i + 1 < p->err_valid) {
	    pacc_pr(&r, &l, ", ");
	    if (i + 2 == p->err_valid) pacc_pr(&r, &l, "or ");
	}
    }
    return PACC_SYM(pos)(p, r);
    //printf("%s\n", r);
    //printf("(column %ld)\n", _pacc->err_col);
}

int PACC_SYM(parse)(struct pacc_parser *_pacc) {
    enum pacc_status _status;
    int _cont = -1, _st, _pacc_any_i, _evaling = 0;
    size_t _x = 0, _x_rule, _pos, _pacc_ev_i;
    uint32_t _pacc_utf_cp;

    _st=124;
    goto top;
    contin:
    _st=_cont;
    PACC_TRACE fprintf(stderr, "continuing in state %d\n", _cont);
    top:
    PACC_TRACE fprintf(stderr, "switch to state %d\n", _st);
    switch(_st) {
      case 124: /* rc */
      PACC_TRACE fprintf(stderr, "rule 124 (rc) col %ld\n", _x);
      _x_rule = _x;
      cur = _pacc_result(_pacc, _x, 124);
      if ((cur->rule & 3) == uncomputed) {
        PACC_TRACE fprintf(stderr, "seq 122 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 122;
        _status = parsed;
        /* bind: l */
        PACC_TRACE fprintf(stderr, "bind 118 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind l @ rule 169, col %ld\n", _x);
        _pacc_save_core(169, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 117;
        _st = 169;
        /* call line */
        goto top;
        case 117: /* return from line */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 124);
        /* end bind: l */
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "expr 121 @ col %ld?\n", _x);
        assert(cur->expr_id == 0);
        cur->expr_id = 121;
        case 121:
        if (_evaling) {
          struct pacc_mid *_pacc_p;
          /* i is 0, type is Node * */
          Node * l;
          PACC_TRACE fprintf(stderr, "121: evaluating\n");
          _pacc_p = cur = _pacc_result(_pacc, _x, 124);
          _pos = 0;
          PACC_TRACE fprintf(stderr, "binding of l: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind l to r169 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 169);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 119;
            _pacc_ev_i = 0; goto eval_loop;
            case 119:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          l = cur->value.u0;
          PACC_TRACE fprintf(stderr, "bound l to r169 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          cur = _pacc_p;
          cur->value.u0=
#line 54 "parse.pacc"
                               ( l )
#line 559 "parse.c"
          ;
          PACC_TRACE fprintf(stderr, "stash " TYPE_PRINTF " to (%ld, 124)\n", cur->value.u0, _x);
          goto _pacc_expr_done;
        }
        case 122:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 122 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        cur->rule = (cur->rule & ~3) | _status;
        cur->remainder = _x;
        if (_pacc->err_col == _x_rule) {
          _pacc->err_valid = 0;
          _pacc_error(_pacc, ".rc", _x_rule);
        }
      }
      goto contin;
      case 146: /* cmdsa */
      PACC_TRACE fprintf(stderr, "rule 146 (cmdsa) col %ld\n", _x);
      _x_rule = _x;
      cur = _pacc_result(_pacc, _x, 146);
      if ((cur->rule & 3) == uncomputed) {
        PACC_TRACE fprintf(stderr, "alt 144 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 144;
        PACC_TRACE fprintf(stderr, "save column registers\n");
        _pacc_Push(_x); _pacc_Push(cur->ev_valid);
        PACC_TRACE fprintf(stderr, "seq 131 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 131;
        _status = parsed;
        /* bind: c */
        PACC_TRACE fprintf(stderr, "bind 126 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind c @ rule 621, col %ld\n", _x);
        _pacc_save_core(621, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 125;
        _st = 621;
        /* call cmd */
        goto top;
        case 125: /* return from cmd */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 146);
        /* end bind: c */
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "lit 127 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "lit 127 @ col %ld => ", _x);
        if (_x+1 <= _pacc->input_length && memcmp(";", _pacc->string + _x, 1) == 0) {
          _status = parsed;
          _x += 1;
        }
        else {
          _pacc_error(_pacc, ".\";\"", _x);
          _status = no_parse;
        }
        PACC_TRACE fprintf(stderr, "lit 127 %ld => %s\n", _x, _status != no_parse ? "yes" : "no");
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "expr 130 @ col %ld?\n", _x);
        assert(cur->expr_id == 0);
        cur->expr_id = 130;
        case 130:
        if (_evaling) {
          struct pacc_mid *_pacc_p;
          /* i is 0, type is struct Node * */
          struct Node * c;
          PACC_TRACE fprintf(stderr, "130: evaluating\n");
          _pacc_p = cur = _pacc_result(_pacc, _x, 146);
          _pos = 0;
          PACC_TRACE fprintf(stderr, "binding of c: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind c to r621 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 621);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 128;
            _pacc_ev_i = 0; goto eval_loop;
            case 128:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          c = cur->value.u3;
          PACC_TRACE fprintf(stderr, "bound c to r621 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          cur = _pacc_p;
          cur->value.u0=
#line 64 "parse.pacc"
                   (c)
#line 651 "parse.c"
          ;
          PACC_TRACE fprintf(stderr, "stash " TYPE_PRINTF " to (%ld, 146)\n", cur->value.u0, _x);
          goto _pacc_expr_done;
        }
        case 131:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 131 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 144 @ col %ld => %s\n", _x, _status!=no_parse?"yes":"no");
        if (_status != no_parse) {
          PACC_TRACE fprintf(stderr, "accept column registers\n");
          _pacc_Discard(cur->ev_valid); _pacc_Discard(_x);
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "restore column registers\n");
        _pacc_Pop(cur->ev_valid); _pacc_Pop(_x);
        PACC_TRACE fprintf(stderr, "save column registers\n");
        _pacc_Push(_x); _pacc_Push(cur->ev_valid);
        PACC_TRACE fprintf(stderr, "col restored to %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 144 @ col %ld? (next alternative)\n", _x);
        PACC_TRACE fprintf(stderr, "seq 143 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 143;
        _status = parsed;
        /* bind: c */
        PACC_TRACE fprintf(stderr, "bind 133 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind c @ rule 621, col %ld\n", _x);
        _pacc_save_core(621, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 132;
        _st = 621;
        /* call cmd */
        goto top;
        case 132: /* return from cmd */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 146);
        /* end bind: c */
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "lit 134 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "lit 134 @ col %ld => ", _x);
        if (_x+1 <= _pacc->input_length && memcmp("&", _pacc->string + _x, 1) == 0) {
          _status = parsed;
          _x += 1;
        }
        else {
          _pacc_error(_pacc, ".\"&\"", _x);
          _status = no_parse;
        }
        PACC_TRACE fprintf(stderr, "lit 134 %ld => %s\n", _x, _status != no_parse ? "yes" : "no");
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "expr 142 @ col %ld?\n", _x);
        assert(cur->expr_id == 0);
        cur->expr_id = 142;
        case 142:
        if (_evaling) {
          struct pacc_mid *_pacc_p;
          /* i is 0, type is struct Node * */
          struct Node * c;
          PACC_TRACE fprintf(stderr, "142: evaluating\n");
          _pacc_p = cur = _pacc_result(_pacc, _x, 146);
          _pos = 0;
          PACC_TRACE fprintf(stderr, "binding of c: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind c to r621 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 621);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 135;
            _pacc_ev_i = 0; goto eval_loop;
            case 135:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          c = cur->value.u3;
          PACC_TRACE fprintf(stderr, "bound c to r621 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          cur = _pacc_p;
          cur->value.u0=
#line 65 "parse.pacc"
              ( c != NULL ? mk(nNowait, c) :  c )
#line 737 "parse.c"
          ;
          PACC_TRACE fprintf(stderr, "stash " TYPE_PRINTF " to (%ld, 146)\n", cur->value.u0, _x);
          goto _pacc_expr_done;
        }
        case 143:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 143 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        if (_status == no_parse) {
          PACC_TRACE fprintf(stderr, "restore column registers\n");
          _pacc_Pop(cur->ev_valid); _pacc_Pop(_x);
        }
        else {
          PACC_TRACE fprintf(stderr, "accept column registers\n");
          _pacc_Discard(cur->ev_valid); _pacc_Discard(_x);
        }
        case 144:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "alt 144 @ col %ld => %s\n", _x, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        cur->rule = (cur->rule & ~3) | _status;
        cur->remainder = _x;
        if (_pacc->err_col == _x_rule) {
          _pacc->err_valid = 0;
          _pacc_error(_pacc, ".cmdsa", _x_rule);
        }
      }
      goto contin;
      case 169: /* line */
      PACC_TRACE fprintf(stderr, "rule 169 (line) col %ld\n", _x);
      _x_rule = _x;
      cur = _pacc_result(_pacc, _x, 169);
      if ((cur->rule & 3) == uncomputed) {
        PACC_TRACE fprintf(stderr, "alt 167 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 167;
        PACC_TRACE fprintf(stderr, "save column registers\n");
        _pacc_Push(_x); _pacc_Push(cur->ev_valid);
        PACC_TRACE fprintf(stderr, "seq 152 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 152;
        _status = parsed;
        /* bind: c */
        PACC_TRACE fprintf(stderr, "bind 148 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind c @ rule 621, col %ld\n", _x);
        _pacc_save_core(621, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 147;
        _st = 621;
        /* call cmd */
        goto top;
        case 147: /* return from cmd */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 169);
        /* end bind: c */
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "expr 151 @ col %ld?\n", _x);
        assert(cur->expr_id == 0);
        cur->expr_id = 151;
        case 151:
        if (_evaling) {
          struct pacc_mid *_pacc_p;
          /* i is 0, type is struct Node * */
          struct Node * c;
          PACC_TRACE fprintf(stderr, "151: evaluating\n");
          _pacc_p = cur = _pacc_result(_pacc, _x, 169);
          _pos = 0;
          PACC_TRACE fprintf(stderr, "binding of c: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind c to r621 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 621);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 149;
            _pacc_ev_i = 0; goto eval_loop;
            case 149:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          c = cur->value.u3;
          PACC_TRACE fprintf(stderr, "bound c to r621 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          cur = _pacc_p;
          cur->value.u0=
#line 68 "parse.pacc"
              (c)
#line 827 "parse.c"
          ;
          PACC_TRACE fprintf(stderr, "stash " TYPE_PRINTF " to (%ld, 169)\n", cur->value.u0, _x);
          goto _pacc_expr_done;
        }
        case 152:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 152 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 167 @ col %ld => %s\n", _x, _status!=no_parse?"yes":"no");
        if (_status != no_parse) {
          PACC_TRACE fprintf(stderr, "accept column registers\n");
          _pacc_Discard(cur->ev_valid); _pacc_Discard(_x);
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "restore column registers\n");
        _pacc_Pop(cur->ev_valid); _pacc_Pop(_x);
        PACC_TRACE fprintf(stderr, "save column registers\n");
        _pacc_Push(_x); _pacc_Push(cur->ev_valid);
        PACC_TRACE fprintf(stderr, "col restored to %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 167 @ col %ld? (next alternative)\n", _x);
        PACC_TRACE fprintf(stderr, "seq 166 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 166;
        _status = parsed;
        /* bind: c */
        PACC_TRACE fprintf(stderr, "bind 154 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind c @ rule 146, col %ld\n", _x);
        _pacc_save_core(146, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 153;
        _st = 146;
        /* call cmdsa */
        goto top;
        case 153: /* return from cmdsa */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 169);
        /* end bind: c */
        if (_status == no_parse) {
          goto contin;
        }
        /* bind: l */
        PACC_TRACE fprintf(stderr, "bind 156 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind l @ rule 169, col %ld\n", _x);
        _pacc_save_core(169, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 155;
        _st = 169;
        /* call line */
        goto top;
        case 155: /* return from line */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 169);
        /* end bind: l */
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "expr 165 @ col %ld?\n", _x);
        assert(cur->expr_id == 0);
        cur->expr_id = 165;
        case 165:
        if (_evaling) {
          struct pacc_mid *_pacc_p;
          /* i is 0, type is Node * */
          Node * c;
          /* i is 1, type is Node * */
          Node * l;
          PACC_TRACE fprintf(stderr, "165: evaluating\n");
          _pacc_p = cur = _pacc_result(_pacc, _x, 169);
          _pos = 0;
          PACC_TRACE fprintf(stderr, "binding of c: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind c to r146 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 146);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 159;
            _pacc_ev_i = 0; goto eval_loop;
            case 159:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          c = cur->value.u0;
          PACC_TRACE fprintf(stderr, "bound c to r146 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          _pos = 1;
          PACC_TRACE fprintf(stderr, "binding of l: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind l to r169 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 169);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 157;
            _pacc_ev_i = 0; goto eval_loop;
            case 157:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          l = cur->value.u0;
          PACC_TRACE fprintf(stderr, "bound l to r169 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          cur = _pacc_p;
          cur->value.u0=
#line 69 "parse.pacc"
                   ( c != NULL ? mk(nBody,c,l) : l )
#line 934 "parse.c"
          ;
          PACC_TRACE fprintf(stderr, "stash " TYPE_PRINTF " to (%ld, 169)\n", cur->value.u0, _x);
          goto _pacc_expr_done;
        }
        case 166:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 166 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        if (_status == no_parse) {
          PACC_TRACE fprintf(stderr, "restore column registers\n");
          _pacc_Pop(cur->ev_valid); _pacc_Pop(_x);
        }
        else {
          PACC_TRACE fprintf(stderr, "accept column registers\n");
          _pacc_Discard(cur->ev_valid); _pacc_Discard(_x);
        }
        case 167:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "alt 167 @ col %ld => %s\n", _x, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        cur->rule = (cur->rule & ~3) | _status;
        cur->remainder = _x;
        if (_pacc->err_col == _x_rule) {
          _pacc->err_valid = 0;
          _pacc_error(_pacc, ".line", _x_rule);
        }
      }
      goto contin;
      case 195: /* body */
      PACC_TRACE fprintf(stderr, "rule 195 (body) col %ld\n", _x);
      _x_rule = _x;
      cur = _pacc_result(_pacc, _x, 195);
      if ((cur->rule & 3) == uncomputed) {
        PACC_TRACE fprintf(stderr, "alt 193 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 193;
        PACC_TRACE fprintf(stderr, "save column registers\n");
        _pacc_Push(_x); _pacc_Push(cur->ev_valid);
        PACC_TRACE fprintf(stderr, "seq 175 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 175;
        _status = parsed;
        /* bind: c */
        PACC_TRACE fprintf(stderr, "bind 171 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind c @ rule 621, col %ld\n", _x);
        _pacc_save_core(621, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 170;
        _st = 621;
        /* call cmd */
        goto top;
        case 170: /* return from cmd */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 195);
        /* end bind: c */
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "expr 174 @ col %ld?\n", _x);
        assert(cur->expr_id == 0);
        cur->expr_id = 174;
        case 174:
        if (_evaling) {
          struct pacc_mid *_pacc_p;
          /* i is 0, type is struct Node * */
          struct Node * c;
          PACC_TRACE fprintf(stderr, "174: evaluating\n");
          _pacc_p = cur = _pacc_result(_pacc, _x, 195);
          _pos = 0;
          PACC_TRACE fprintf(stderr, "binding of c: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind c to r621 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 621);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 172;
            _pacc_ev_i = 0; goto eval_loop;
            case 172:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          c = cur->value.u3;
          PACC_TRACE fprintf(stderr, "bound c to r621 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          cur = _pacc_p;
          cur->value.u0=
#line 72 "parse.pacc"
              (c)
#line 1024 "parse.c"
          ;
          PACC_TRACE fprintf(stderr, "stash " TYPE_PRINTF " to (%ld, 195)\n", cur->value.u0, _x);
          goto _pacc_expr_done;
        }
        case 175:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 175 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 193 @ col %ld => %s\n", _x, _status!=no_parse?"yes":"no");
        if (_status != no_parse) {
          PACC_TRACE fprintf(stderr, "accept column registers\n");
          _pacc_Discard(cur->ev_valid); _pacc_Discard(_x);
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "restore column registers\n");
        _pacc_Pop(cur->ev_valid); _pacc_Pop(_x);
        PACC_TRACE fprintf(stderr, "save column registers\n");
        _pacc_Push(_x); _pacc_Push(cur->ev_valid);
        PACC_TRACE fprintf(stderr, "col restored to %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 193 @ col %ld? (next alternative)\n", _x);
        PACC_TRACE fprintf(stderr, "seq 192 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 192;
        _status = parsed;
        /* bind: c */
        PACC_TRACE fprintf(stderr, "bind 177 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind c @ rule 211, col %ld\n", _x);
        _pacc_save_core(211, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 176;
        _st = 211;
        /* call cmdsan */
        goto top;
        case 176: /* return from cmdsan */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 195);
        /* end bind: c */
        if (_status == no_parse) {
          goto contin;
        }
        /* bind: b */
        PACC_TRACE fprintf(stderr, "bind 179 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind b @ rule 195, col %ld\n", _x);
        _pacc_save_core(195, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 178;
        _st = 195;
        /* call body */
        goto top;
        case 178: /* return from body */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 195);
        /* end bind: b */
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "expr 191 @ col %ld?\n", _x);
        assert(cur->expr_id == 0);
        cur->expr_id = 191;
        case 191:
        if (_evaling) {
          struct pacc_mid *_pacc_p;
          /* i is 0, type is Node * */
          Node * c;
          /* i is 1, type is Node * */
          Node * b;
          PACC_TRACE fprintf(stderr, "191: evaluating\n");
          _pacc_p = cur = _pacc_result(_pacc, _x, 195);
          _pos = 0;
          PACC_TRACE fprintf(stderr, "binding of c: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind c to r211 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 211);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 181;
            _pacc_ev_i = 0; goto eval_loop;
            case 181:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          c = cur->value.u0;
          PACC_TRACE fprintf(stderr, "bound c to r211 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          _pos = 1;
          PACC_TRACE fprintf(stderr, "binding of b: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind b to r195 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 195);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 180;
            _pacc_ev_i = 0; goto eval_loop;
            case 180:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          b = cur->value.u0;
          PACC_TRACE fprintf(stderr, "bound b to r195 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          cur = _pacc_p;
          cur->value.u0=
#line 73 "parse.pacc"
                   ( c == NULL ? b : b == NULL ? c : mk(nBody,c,b) )
#line 1131 "parse.c"
          ;
          PACC_TRACE fprintf(stderr, "stash " TYPE_PRINTF " to (%ld, 195)\n", cur->value.u0, _x);
          goto _pacc_expr_done;
        }
        case 192:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 192 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        if (_status == no_parse) {
          PACC_TRACE fprintf(stderr, "restore column registers\n");
          _pacc_Pop(cur->ev_valid); _pacc_Pop(_x);
        }
        else {
          PACC_TRACE fprintf(stderr, "accept column registers\n");
          _pacc_Discard(cur->ev_valid); _pacc_Discard(_x);
        }
        case 193:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "alt 193 @ col %ld => %s\n", _x, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        cur->rule = (cur->rule & ~3) | _status;
        cur->remainder = _x;
        if (_pacc->err_col == _x_rule) {
          _pacc->err_valid = 0;
          _pacc_error(_pacc, ".body", _x_rule);
        }
      }
      goto contin;
      case 211: /* cmdsan */
      PACC_TRACE fprintf(stderr, "rule 211 (cmdsan) col %ld\n", _x);
      _x_rule = _x;
      cur = _pacc_result(_pacc, _x, 211);
      if ((cur->rule & 3) == uncomputed) {
        PACC_TRACE fprintf(stderr, "alt 209 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 209;
        PACC_TRACE fprintf(stderr, "save column registers\n");
        _pacc_Push(_x); _pacc_Push(cur->ev_valid);
        PACC_TRACE fprintf(stderr, "seq 201 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 201;
        _status = parsed;
        /* bind: c */
        PACC_TRACE fprintf(stderr, "bind 197 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind c @ rule 146, col %ld\n", _x);
        _pacc_save_core(146, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 196;
        _st = 146;
        /* call cmdsa */
        goto top;
        case 196: /* return from cmdsa */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 211);
        /* end bind: c */
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "expr 200 @ col %ld?\n", _x);
        assert(cur->expr_id == 0);
        cur->expr_id = 200;
        case 200:
        if (_evaling) {
          struct pacc_mid *_pacc_p;
          /* i is 0, type is Node * */
          Node * c;
          PACC_TRACE fprintf(stderr, "200: evaluating\n");
          _pacc_p = cur = _pacc_result(_pacc, _x, 211);
          _pos = 0;
          PACC_TRACE fprintf(stderr, "binding of c: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind c to r146 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 146);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 198;
            _pacc_ev_i = 0; goto eval_loop;
            case 198:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          c = cur->value.u0;
          PACC_TRACE fprintf(stderr, "bound c to r146 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          cur = _pacc_p;
          cur->value.u0=
#line 75 "parse.pacc"
                  (c)
#line 1221 "parse.c"
          ;
          PACC_TRACE fprintf(stderr, "stash " TYPE_PRINTF " to (%ld, 211)\n", cur->value.u0, _x);
          goto _pacc_expr_done;
        }
        case 201:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 201 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 209 @ col %ld => %s\n", _x, _status!=no_parse?"yes":"no");
        if (_status != no_parse) {
          PACC_TRACE fprintf(stderr, "accept column registers\n");
          _pacc_Discard(cur->ev_valid); _pacc_Discard(_x);
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "restore column registers\n");
        _pacc_Pop(cur->ev_valid); _pacc_Pop(_x);
        PACC_TRACE fprintf(stderr, "save column registers\n");
        _pacc_Push(_x); _pacc_Push(cur->ev_valid);
        PACC_TRACE fprintf(stderr, "col restored to %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 209 @ col %ld? (next alternative)\n", _x);
        PACC_TRACE fprintf(stderr, "seq 208 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 208;
        _status = parsed;
        /* bind: c */
        PACC_TRACE fprintf(stderr, "bind 203 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind c @ rule 621, col %ld\n", _x);
        _pacc_save_core(621, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 202;
        _st = 621;
        /* call cmd */
        goto top;
        case 202: /* return from cmd */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 211);
        /* end bind: c */
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "lit 204 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "lit 204 @ col %ld => ", _x);
        if (_x+1 <= _pacc->input_length && memcmp("\n", _pacc->string + _x, 1) == 0) {
          _status = parsed;
          _x += 1;
        }
        else {
          _pacc_error(_pacc, ".\"\n\"", _x);
          _status = no_parse;
        }
        PACC_TRACE fprintf(stderr, "lit 204 %ld => %s\n", _x, _status != no_parse ? "yes" : "no");
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "expr 207 @ col %ld?\n", _x);
        assert(cur->expr_id == 0);
        cur->expr_id = 207;
        case 207:
        if (_evaling) {
          struct pacc_mid *_pacc_p;
          /* i is 0, type is struct Node * */
          struct Node * c;
          PACC_TRACE fprintf(stderr, "207: evaluating\n");
          _pacc_p = cur = _pacc_result(_pacc, _x, 211);
          _pos = 0;
          PACC_TRACE fprintf(stderr, "binding of c: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind c to r621 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 621);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 205;
            _pacc_ev_i = 0; goto eval_loop;
            case 205:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          c = cur->value.u3;
          PACC_TRACE fprintf(stderr, "bound c to r621 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          cur = _pacc_p;
          cur->value.u0=
#line 76 "parse.pacc"
               ( c /* $1; if (!heredoc(0)) YYABORT; } get h.d. on \n */ )
#line 1307 "parse.c"
          ;
          PACC_TRACE fprintf(stderr, "stash " TYPE_PRINTF " to (%ld, 211)\n", cur->value.u0, _x);
          goto _pacc_expr_done;
        }
        case 208:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 208 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        if (_status == no_parse) {
          PACC_TRACE fprintf(stderr, "restore column registers\n");
          _pacc_Pop(cur->ev_valid); _pacc_Pop(_x);
        }
        else {
          PACC_TRACE fprintf(stderr, "accept column registers\n");
          _pacc_Discard(cur->ev_valid); _pacc_Discard(_x);
        }
        case 209:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "alt 209 @ col %ld => %s\n", _x, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        cur->rule = (cur->rule & ~3) | _status;
        cur->remainder = _x;
        if (_pacc->err_col == _x_rule) {
          _pacc->err_valid = 0;
          _pacc_error(_pacc, ".cmdsan", _x_rule);
        }
      }
      goto contin;
      case 221: /* brace */
      PACC_TRACE fprintf(stderr, "rule 221 (brace) col %ld\n", _x);
      _x_rule = _x;
      cur = _pacc_result(_pacc, _x, 221);
      if ((cur->rule & 3) == uncomputed) {
        PACC_TRACE fprintf(stderr, "seq 219 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 219;
        _status = parsed;
        PACC_TRACE fprintf(stderr, "lit 212 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "lit 212 @ col %ld => ", _x);
        if (_x+1 <= _pacc->input_length && memcmp("{", _pacc->string + _x, 1) == 0) {
          _status = parsed;
          _x += 1;
        }
        else {
          _pacc_error(_pacc, ".\"{\"", _x);
          _status = no_parse;
        }
        PACC_TRACE fprintf(stderr, "lit 212 %ld => %s\n", _x, _status != no_parse ? "yes" : "no");
        if (_status == no_parse) {
          goto contin;
        }
        /* bind: b */
        PACC_TRACE fprintf(stderr, "bind 214 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind b @ rule 195, col %ld\n", _x);
        _pacc_save_core(195, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 213;
        _st = 195;
        /* call body */
        goto top;
        case 213: /* return from body */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 221);
        /* end bind: b */
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "lit 215 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "lit 215 @ col %ld => ", _x);
        if (_x+1 <= _pacc->input_length && memcmp("}", _pacc->string + _x, 1) == 0) {
          _status = parsed;
          _x += 1;
        }
        else {
          _pacc_error(_pacc, ".\"}\"", _x);
          _status = no_parse;
        }
        PACC_TRACE fprintf(stderr, "lit 215 %ld => %s\n", _x, _status != no_parse ? "yes" : "no");
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "expr 218 @ col %ld?\n", _x);
        assert(cur->expr_id == 0);
        cur->expr_id = 218;
        case 218:
        if (_evaling) {
          struct pacc_mid *_pacc_p;
          /* i is 0, type is Node * */
          Node * b;
          PACC_TRACE fprintf(stderr, "218: evaluating\n");
          _pacc_p = cur = _pacc_result(_pacc, _x, 221);
          _pos = 0;
          PACC_TRACE fprintf(stderr, "binding of b: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind b to r195 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 195);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 216;
            _pacc_ev_i = 0; goto eval_loop;
            case 216:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          b = cur->value.u0;
          PACC_TRACE fprintf(stderr, "bound b to r195 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          cur = _pacc_p;
          cur->value.u0=
#line 78 "parse.pacc"
                        (b)
#line 1420 "parse.c"
          ;
          PACC_TRACE fprintf(stderr, "stash " TYPE_PRINTF " to (%ld, 221)\n", cur->value.u0, _x);
          goto _pacc_expr_done;
        }
        case 219:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 219 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        cur->rule = (cur->rule & ~3) | _status;
        cur->remainder = _x;
        if (_pacc->err_col == _x_rule) {
          _pacc->err_valid = 0;
          _pacc_error(_pacc, ".brace", _x_rule);
        }
      }
      goto contin;
      case 231: /* paren */
      PACC_TRACE fprintf(stderr, "rule 231 (paren) col %ld\n", _x);
      _x_rule = _x;
      cur = _pacc_result(_pacc, _x, 231);
      if ((cur->rule & 3) == uncomputed) {
        PACC_TRACE fprintf(stderr, "seq 229 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 229;
        _status = parsed;
        PACC_TRACE fprintf(stderr, "lit 222 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "lit 222 @ col %ld => ", _x);
        if (_x+1 <= _pacc->input_length && memcmp("(", _pacc->string + _x, 1) == 0) {
          _status = parsed;
          _x += 1;
        }
        else {
          _pacc_error(_pacc, ".\"(\"", _x);
          _status = no_parse;
        }
        PACC_TRACE fprintf(stderr, "lit 222 %ld => %s\n", _x, _status != no_parse ? "yes" : "no");
        if (_status == no_parse) {
          goto contin;
        }
        /* bind: b */
        PACC_TRACE fprintf(stderr, "bind 224 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind b @ rule 195, col %ld\n", _x);
        _pacc_save_core(195, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 223;
        _st = 195;
        /* call body */
        goto top;
        case 223: /* return from body */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 231);
        /* end bind: b */
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "lit 225 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "lit 225 @ col %ld => ", _x);
        if (_x+1 <= _pacc->input_length && memcmp(")", _pacc->string + _x, 1) == 0) {
          _status = parsed;
          _x += 1;
        }
        else {
          _pacc_error(_pacc, ".\")\"", _x);
          _status = no_parse;
        }
        PACC_TRACE fprintf(stderr, "lit 225 %ld => %s\n", _x, _status != no_parse ? "yes" : "no");
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "expr 228 @ col %ld?\n", _x);
        assert(cur->expr_id == 0);
        cur->expr_id = 228;
        case 228:
        if (_evaling) {
          struct pacc_mid *_pacc_p;
          /* i is 0, type is Node * */
          Node * b;
          PACC_TRACE fprintf(stderr, "228: evaluating\n");
          _pacc_p = cur = _pacc_result(_pacc, _x, 231);
          _pos = 0;
          PACC_TRACE fprintf(stderr, "binding of b: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind b to r195 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 195);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 226;
            _pacc_ev_i = 0; goto eval_loop;
            case 226:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          b = cur->value.u0;
          PACC_TRACE fprintf(stderr, "bound b to r195 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          cur = _pacc_p;
          cur->value.u0=
#line 80 "parse.pacc"
                        (b)
#line 1521 "parse.c"
          ;
          PACC_TRACE fprintf(stderr, "stash " TYPE_PRINTF " to (%ld, 231)\n", cur->value.u0, _x);
          goto _pacc_expr_done;
        }
        case 229:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 229 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        cur->rule = (cur->rule & ~3) | _status;
        cur->remainder = _x;
        if (_pacc->err_col == _x_rule) {
          _pacc->err_valid = 0;
          _pacc_error(_pacc, ".paren", _x_rule);
        }
      }
      goto contin;
      case 245: /* assign */
      PACC_TRACE fprintf(stderr, "rule 245 (assign) col %ld\n", _x);
      _x_rule = _x;
      cur = _pacc_result(_pacc, _x, 245);
      if ((cur->rule & 3) == uncomputed) {
        PACC_TRACE fprintf(stderr, "seq 243 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 243;
        _status = parsed;
        /* bind: f */
        PACC_TRACE fprintf(stderr, "bind 233 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind f @ rule 666, col %ld\n", _x);
        _pacc_save_core(666, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 232;
        _st = 666;
        /* call First */
        goto top;
        case 232: /* return from First */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 245);
        /* end bind: f */
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "lit 234 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "lit 234 @ col %ld => ", _x);
        if (_x+1 <= _pacc->input_length && memcmp("=", _pacc->string + _x, 1) == 0) {
          _status = parsed;
          _x += 1;
        }
        else {
          _pacc_error(_pacc, ".\"=\"", _x);
          _status = no_parse;
        }
        PACC_TRACE fprintf(stderr, "lit 234 %ld => %s\n", _x, _status != no_parse ? "yes" : "no");
        if (_status == no_parse) {
          goto contin;
        }
        /* bind: w */
        PACC_TRACE fprintf(stderr, "bind 236 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind w @ rule 695, col %ld\n", _x);
        _pacc_save_core(695, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 235;
        _st = 695;
        /* call word */
        goto top;
        case 235: /* return from word */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 245);
        /* end bind: w */
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "expr 242 @ col %ld?\n", _x);
        assert(cur->expr_id == 0);
        cur->expr_id = 242;
        case 242:
        if (_evaling) {
          struct pacc_mid *_pacc_p;
          /* i is 0, type is struct Node * */
          struct Node * f;
          /* i is 1, type is struct Node * */
          struct Node * w;
          PACC_TRACE fprintf(stderr, "242: evaluating\n");
          _pacc_p = cur = _pacc_result(_pacc, _x, 245);
          _pos = 0;
          PACC_TRACE fprintf(stderr, "binding of f: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind f to r666 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 666);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 238;
            _pacc_ev_i = 0; goto eval_loop;
            case 238:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          f = cur->value.u3;
          PACC_TRACE fprintf(stderr, "bound f to r666 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          _pos = 1;
          PACC_TRACE fprintf(stderr, "binding of w: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind w to r695 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 695);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 237;
            _pacc_ev_i = 0; goto eval_loop;
            case 237:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          w = cur->value.u3;
          PACC_TRACE fprintf(stderr, "bound w to r695 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          cur = _pacc_p;
          cur->value.u0=
#line 82 "parse.pacc"
                            ( mk(nAssign, f, w) )
#line 1643 "parse.c"
          ;
          PACC_TRACE fprintf(stderr, "stash " TYPE_PRINTF " to (%ld, 245)\n", cur->value.u0, _x);
          goto _pacc_expr_done;
        }
        case 243:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 243 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        cur->rule = (cur->rule & ~3) | _status;
        cur->remainder = _x;
        if (_pacc->err_col == _x_rule) {
          _pacc->err_valid = 0;
          _pacc_error(_pacc, ".assign", _x_rule);
        }
      }
      goto contin;
      case 262: /* epilog */
      PACC_TRACE fprintf(stderr, "rule 262 (epilog) col %ld\n", _x);
      _x_rule = _x;
      cur = _pacc_result(_pacc, _x, 262);
      if ((cur->rule & 3) == uncomputed) {
        PACC_TRACE fprintf(stderr, "alt 260 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 260;
        PACC_TRACE fprintf(stderr, "save column registers\n");
        _pacc_Push(_x); _pacc_Push(cur->ev_valid);
        PACC_TRACE fprintf(stderr, "seq 248 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 248;
        _status = parsed;
        PACC_TRACE fprintf(stderr, "expr 247 @ col %ld?\n", _x);
        assert(cur->expr_id == 0);
        cur->expr_id = 247;
        case 247:
        if (_evaling) {
          struct pacc_mid *_pacc_p;
          PACC_TRACE fprintf(stderr, "247: evaluating\n");
          _pacc_p = cur = _pacc_result(_pacc, _x, 262);
          cur = _pacc_p;
          cur->value.u0=
#line 84 "parse.pacc"
            (0)
#line 1686 "parse.c"
          ;
          PACC_TRACE fprintf(stderr, "stash " TYPE_PRINTF " to (%ld, 262)\n", cur->value.u0, _x);
          goto _pacc_expr_done;
        }
        case 248:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 248 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 260 @ col %ld => %s\n", _x, _status!=no_parse?"yes":"no");
        if (_status != no_parse) {
          PACC_TRACE fprintf(stderr, "accept column registers\n");
          _pacc_Discard(cur->ev_valid); _pacc_Discard(_x);
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "restore column registers\n");
        _pacc_Pop(cur->ev_valid); _pacc_Pop(_x);
        PACC_TRACE fprintf(stderr, "save column registers\n");
        _pacc_Push(_x); _pacc_Push(cur->ev_valid);
        PACC_TRACE fprintf(stderr, "col restored to %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 260 @ col %ld? (next alternative)\n", _x);
        PACC_TRACE fprintf(stderr, "seq 259 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 259;
        _status = parsed;
        /* bind: r */
        PACC_TRACE fprintf(stderr, "bind 250 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind r @ rule 298, col %ld\n", _x);
        _pacc_save_core(298, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 249;
        _st = 298;
        /* call redir */
        goto top;
        case 249: /* return from redir */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 262);
        /* end bind: r */
        if (_status == no_parse) {
          goto contin;
        }
        /* bind: e */
        PACC_TRACE fprintf(stderr, "bind 252 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind e @ rule 262, col %ld\n", _x);
        _pacc_save_core(262, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 251;
        _st = 262;
        /* call epilog */
        goto top;
        case 251: /* return from epilog */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 262);
        /* end bind: e */
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "expr 258 @ col %ld?\n", _x);
        assert(cur->expr_id == 0);
        cur->expr_id = 258;
        case 258:
        if (_evaling) {
          struct pacc_mid *_pacc_p;
          /* i is 0, type is Node * */
          Node * r;
          /* i is 1, type is Node * */
          Node * e;
          PACC_TRACE fprintf(stderr, "258: evaluating\n");
          _pacc_p = cur = _pacc_result(_pacc, _x, 262);
          _pos = 0;
          PACC_TRACE fprintf(stderr, "binding of r: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind r to r298 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 298);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 254;
            _pacc_ev_i = 0; goto eval_loop;
            case 254:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          r = cur->value.u0;
          PACC_TRACE fprintf(stderr, "bound r to r298 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          _pos = 1;
          PACC_TRACE fprintf(stderr, "binding of e: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind e to r262 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 262);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 253;
            _pacc_ev_i = 0; goto eval_loop;
            case 253:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          e = cur->value.u0;
          PACC_TRACE fprintf(stderr, "bound e to r262 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          cur = _pacc_p;
          cur->value.u0=
#line 85 "parse.pacc"
                     ( mk(nEpilog, r, e) )
#line 1793 "parse.c"
          ;
          PACC_TRACE fprintf(stderr, "stash " TYPE_PRINTF " to (%ld, 262)\n", cur->value.u0, _x);
          goto _pacc_expr_done;
        }
        case 259:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 259 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        if (_status == no_parse) {
          PACC_TRACE fprintf(stderr, "restore column registers\n");
          _pacc_Pop(cur->ev_valid); _pacc_Pop(_x);
        }
        else {
          PACC_TRACE fprintf(stderr, "accept column registers\n");
          _pacc_Discard(cur->ev_valid); _pacc_Discard(_x);
        }
        case 260:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "alt 260 @ col %ld => %s\n", _x, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        cur->rule = (cur->rule & ~3) | _status;
        cur->remainder = _x;
        if (_pacc->err_col == _x_rule) {
          _pacc->err_valid = 0;
          _pacc_error(_pacc, ".epilog", _x_rule);
        }
      }
      goto contin;
      case 298: /* redir */
      PACC_TRACE fprintf(stderr, "rule 298 (redir) col %ld\n", _x);
      _x_rule = _x;
      cur = _pacc_result(_pacc, _x, 298);
      if ((cur->rule & 3) == uncomputed) {
        PACC_TRACE fprintf(stderr, "alt 296 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 296;
        PACC_TRACE fprintf(stderr, "save column registers\n");
        _pacc_Push(_x); _pacc_Push(cur->ev_valid);
        PACC_TRACE fprintf(stderr, "seq 279 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 279;
        _status = parsed;
        /* bind: r */
        PACC_TRACE fprintf(stderr, "bind 264 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind r @ rule 326, col %ld\n", _x);
        _pacc_save_core(326, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 263;
        _st = 326;
        /* call Redir */
        goto top;
        case 263: /* return from Redir */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 298);
        /* end bind: r */
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "lit 265 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "lit 265 @ col %ld => ", _x);
        if (_x+1 <= _pacc->input_length && memcmp("[", _pacc->string + _x, 1) == 0) {
          _status = parsed;
          _x += 1;
        }
        else {
          _pacc_error(_pacc, ".\"[\"", _x);
          _status = no_parse;
        }
        PACC_TRACE fprintf(stderr, "lit 265 %ld => %s\n", _x, _status != no_parse ? "yes" : "no");
        if (_status == no_parse) {
          goto contin;
        }
        /* bind: l */
        PACC_TRACE fprintf(stderr, "bind 267 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind l @ rule 340, col %ld\n", _x);
        _pacc_save_core(340, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 266;
        _st = 340;
        /* call Decimal */
        goto top;
        case 266: /* return from Decimal */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 298);
        /* end bind: l */
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "lit 268 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "lit 268 @ col %ld => ", _x);
        if (_x+1 <= _pacc->input_length && memcmp("=", _pacc->string + _x, 1) == 0) {
          _status = parsed;
          _x += 1;
        }
        else {
          _pacc_error(_pacc, ".\"=\"", _x);
          _status = no_parse;
        }
        PACC_TRACE fprintf(stderr, "lit 268 %ld => %s\n", _x, _status != no_parse ? "yes" : "no");
        if (_status == no_parse) {
          goto contin;
        }
        /* bind: r */
        PACC_TRACE fprintf(stderr, "bind 270 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind r @ rule 340, col %ld\n", _x);
        _pacc_save_core(340, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 269;
        _st = 340;
        /* call Decimal */
        goto top;
        case 269: /* return from Decimal */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 298);
        /* end bind: r */
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "lit 271 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "lit 271 @ col %ld => ", _x);
        if (_x+1 <= _pacc->input_length && memcmp("]", _pacc->string + _x, 1) == 0) {
          _status = parsed;
          _x += 1;
        }
        else {
          _pacc_error(_pacc, ".\"]\"", _x);
          _status = no_parse;
        }
        PACC_TRACE fprintf(stderr, "lit 271 %ld => %s\n", _x, _status != no_parse ? "yes" : "no");
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "expr 278 @ col %ld?\n", _x);
        assert(cur->expr_id == 0);
        cur->expr_id = 278;
        case 278:
        if (_evaling) {
          struct pacc_mid *_pacc_p;
          /* i is 1, type is int */
          int l;
          /* i is 2, type is int */
          int r;
          PACC_TRACE fprintf(stderr, "278: evaluating\n");
          _pacc_p = cur = _pacc_result(_pacc, _x, 298);
          _pos = 1;
          PACC_TRACE fprintf(stderr, "binding of l: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind l to r340 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 340);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 273;
            _pacc_ev_i = 0; goto eval_loop;
            case 273:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          l = cur->value.u2;
          PACC_TRACE fprintf(stderr, "bound l to r340 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          _pos = 2;
          PACC_TRACE fprintf(stderr, "binding of r: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind r to r340 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 340);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 272;
            _pacc_ev_i = 0; goto eval_loop;
            case 272:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          r = cur->value.u2;
          PACC_TRACE fprintf(stderr, "bound r to r340 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          cur = _pacc_p;
          cur->value.u0=
#line 88 "parse.pacc"
                                                ( mk(nDup, r, l, r) )
#line 1980 "parse.c"
          ;
          PACC_TRACE fprintf(stderr, "stash " TYPE_PRINTF " to (%ld, 298)\n", cur->value.u0, _x);
          goto _pacc_expr_done;
        }
        case 279:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 279 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 296 @ col %ld => %s\n", _x, _status!=no_parse?"yes":"no");
        if (_status != no_parse) {
          PACC_TRACE fprintf(stderr, "accept column registers\n");
          _pacc_Discard(cur->ev_valid); _pacc_Discard(_x);
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "restore column registers\n");
        _pacc_Pop(cur->ev_valid); _pacc_Pop(_x);
        PACC_TRACE fprintf(stderr, "save column registers\n");
        _pacc_Push(_x); _pacc_Push(cur->ev_valid);
        PACC_TRACE fprintf(stderr, "col restored to %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 296 @ col %ld? (next alternative)\n", _x);
        PACC_TRACE fprintf(stderr, "seq 295 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 295;
        _status = parsed;
        /* bind: r */
        PACC_TRACE fprintf(stderr, "bind 281 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind r @ rule 326, col %ld\n", _x);
        _pacc_save_core(326, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 280;
        _st = 326;
        /* call Redir */
        goto top;
        case 280: /* return from Redir */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 298);
        /* end bind: r */
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "lit 282 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "lit 282 @ col %ld => ", _x);
        if (_x+1 <= _pacc->input_length && memcmp("[", _pacc->string + _x, 1) == 0) {
          _status = parsed;
          _x += 1;
        }
        else {
          _pacc_error(_pacc, ".\"[\"", _x);
          _status = no_parse;
        }
        PACC_TRACE fprintf(stderr, "lit 282 %ld => %s\n", _x, _status != no_parse ? "yes" : "no");
        if (_status == no_parse) {
          goto contin;
        }
        /* bind: d */
        PACC_TRACE fprintf(stderr, "bind 284 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind d @ rule 340, col %ld\n", _x);
        _pacc_save_core(340, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 283;
        _st = 340;
        /* call Decimal */
        goto top;
        case 283: /* return from Decimal */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 298);
        /* end bind: d */
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "lit 285 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "lit 285 @ col %ld => ", _x);
        if (_x+1 <= _pacc->input_length && memcmp("]", _pacc->string + _x, 1) == 0) {
          _status = parsed;
          _x += 1;
        }
        else {
          _pacc_error(_pacc, ".\"]\"", _x);
          _status = no_parse;
        }
        PACC_TRACE fprintf(stderr, "lit 285 %ld => %s\n", _x, _status != no_parse ? "yes" : "no");
        if (_status == no_parse) {
          goto contin;
        }
        /* bind: w */
        PACC_TRACE fprintf(stderr, "bind 287 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind w @ rule 695, col %ld\n", _x);
        _pacc_save_core(695, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 286;
        _st = 695;
        /* call word */
        goto top;
        case 286: /* return from word */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 298);
        /* end bind: w */
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "expr 294 @ col %ld?\n", _x);
        assert(cur->expr_id == 0);
        cur->expr_id = 294;
        case 294:
        if (_evaling) {
          struct pacc_mid *_pacc_p;
          /* i is 0, type is redirtype */
          redirtype r;
          /* i is 1, type is int */
          int d;
          /* i is 2, type is struct Node * */
          struct Node * w;
          PACC_TRACE fprintf(stderr, "294: evaluating\n");
          _pacc_p = cur = _pacc_result(_pacc, _x, 298);
          _pos = 0;
          PACC_TRACE fprintf(stderr, "binding of r: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind r to r326 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 326);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 290;
            _pacc_ev_i = 0; goto eval_loop;
            case 290:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          r = cur->value.u1;
          PACC_TRACE fprintf(stderr, "bound r to r326 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          _pos = 1;
          PACC_TRACE fprintf(stderr, "binding of d: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind d to r340 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 340);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 289;
            _pacc_ev_i = 0; goto eval_loop;
            case 289:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          d = cur->value.u2;
          PACC_TRACE fprintf(stderr, "bound d to r340 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          _pos = 2;
          PACC_TRACE fprintf(stderr, "binding of w: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind w to r695 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 695);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 288;
            _pacc_ev_i = 0; goto eval_loop;
            case 288:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          w = cur->value.u3;
          PACC_TRACE fprintf(stderr, "bound w to r695 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          cur = _pacc_p;
          cur->value.u0=
#line 89 "parse.pacc"
                                     ( mk(nRedir, r, d, w)
				  //if ($1.type == rHeredoc && !qdoc($2, $$)) YYABORT; /* queue heredocs up */
				)
#line 2152 "parse.c"
          ;
          PACC_TRACE fprintf(stderr, "stash " TYPE_PRINTF " to (%ld, 298)\n", cur->value.u0, _x);
          goto _pacc_expr_done;
        }
        case 295:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 295 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        if (_status == no_parse) {
          PACC_TRACE fprintf(stderr, "restore column registers\n");
          _pacc_Pop(cur->ev_valid); _pacc_Pop(_x);
        }
        else {
          PACC_TRACE fprintf(stderr, "accept column registers\n");
          _pacc_Discard(cur->ev_valid); _pacc_Discard(_x);
        }
        case 296:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "alt 296 @ col %ld => %s\n", _x, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        cur->rule = (cur->rule & ~3) | _status;
        cur->remainder = _x;
        if (_pacc->err_col == _x_rule) {
          _pacc->err_valid = 0;
          _pacc_error(_pacc, ".redir", _x_rule);
        }
      }
      goto contin;
      case 326: /* Redir */
      PACC_TRACE fprintf(stderr, "rule 326 (Redir) col %ld\n", _x);
      _x_rule = _x;
      cur = _pacc_result(_pacc, _x, 326);
      if ((cur->rule & 3) == uncomputed) {
        PACC_TRACE fprintf(stderr, "alt 324 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 324;
        PACC_TRACE fprintf(stderr, "save column registers\n");
        _pacc_Push(_x); _pacc_Push(cur->ev_valid);
        PACC_TRACE fprintf(stderr, "seq 303 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 303;
        _status = parsed;
        PACC_TRACE fprintf(stderr, "lit 299 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "lit 299 @ col %ld => ", _x);
        if (_x+3 <= _pacc->input_length && memcmp("<<<", _pacc->string + _x, 3) == 0) {
          _status = parsed;
          _x += 3;
        }
        else {
          _pacc_error(_pacc, ".\"<<<\"", _x);
          _status = no_parse;
        }
        PACC_TRACE fprintf(stderr, "lit 299 %ld => %s\n", _x, _status != no_parse ? "yes" : "no");
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "expr 302 @ col %ld?\n", _x);
        assert(cur->expr_id == 0);
        cur->expr_id = 302;
        case 302:
        if (_evaling) {
          struct pacc_mid *_pacc_p;
          PACC_TRACE fprintf(stderr, "302: evaluating\n");
          _pacc_p = cur = _pacc_result(_pacc, _x, 326);
          cur = _pacc_p;
          cur->value.u1=
#line 99 "parse.pacc"
             (rHerestring)
#line 2221 "parse.c"
          ;
          PACC_TRACE fprintf(stderr, "stash " TYPE_PRINTF " to (%ld, 326)\n", cur->value.u0, _x);
          goto _pacc_expr_done;
        }
        case 303:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 303 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 324 @ col %ld => %s\n", _x, _status!=no_parse?"yes":"no");
        if (_status != no_parse) {
          PACC_TRACE fprintf(stderr, "accept column registers\n");
          _pacc_Discard(cur->ev_valid); _pacc_Discard(_x);
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "restore column registers\n");
        _pacc_Pop(cur->ev_valid); _pacc_Pop(_x);
        PACC_TRACE fprintf(stderr, "save column registers\n");
        _pacc_Push(_x); _pacc_Push(cur->ev_valid);
        PACC_TRACE fprintf(stderr, "col restored to %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 324 @ col %ld? (next alternative)\n", _x);
        PACC_TRACE fprintf(stderr, "seq 308 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 308;
        _status = parsed;
        PACC_TRACE fprintf(stderr, "lit 304 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "lit 304 @ col %ld => ", _x);
        if (_x+2 <= _pacc->input_length && memcmp("<<", _pacc->string + _x, 2) == 0) {
          _status = parsed;
          _x += 2;
        }
        else {
          _pacc_error(_pacc, ".\"<<\"", _x);
          _status = no_parse;
        }
        PACC_TRACE fprintf(stderr, "lit 304 %ld => %s\n", _x, _status != no_parse ? "yes" : "no");
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "expr 307 @ col %ld?\n", _x);
        assert(cur->expr_id == 0);
        cur->expr_id = 307;
        case 307:
        if (_evaling) {
          struct pacc_mid *_pacc_p;
          PACC_TRACE fprintf(stderr, "307: evaluating\n");
          _pacc_p = cur = _pacc_result(_pacc, _x, 326);
          cur = _pacc_p;
          cur->value.u1=
#line 100 "parse.pacc"
            (rHeredoc)
#line 2272 "parse.c"
          ;
          PACC_TRACE fprintf(stderr, "stash " TYPE_PRINTF " to (%ld, 326)\n", cur->value.u0, _x);
          goto _pacc_expr_done;
        }
        case 308:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 308 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 324 @ col %ld => %s\n", _x, _status!=no_parse?"yes":"no");
        if (_status != no_parse) {
          PACC_TRACE fprintf(stderr, "accept column registers\n");
          _pacc_Discard(cur->ev_valid); _pacc_Discard(_x);
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "restore column registers\n");
        _pacc_Pop(cur->ev_valid); _pacc_Pop(_x);
        PACC_TRACE fprintf(stderr, "save column registers\n");
        _pacc_Push(_x); _pacc_Push(cur->ev_valid);
        PACC_TRACE fprintf(stderr, "col restored to %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 324 @ col %ld? (next alternative)\n", _x);
        PACC_TRACE fprintf(stderr, "seq 313 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 313;
        _status = parsed;
        PACC_TRACE fprintf(stderr, "lit 309 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "lit 309 @ col %ld => ", _x);
        if (_x+1 <= _pacc->input_length && memcmp("<", _pacc->string + _x, 1) == 0) {
          _status = parsed;
          _x += 1;
        }
        else {
          _pacc_error(_pacc, ".\"<\"", _x);
          _status = no_parse;
        }
        PACC_TRACE fprintf(stderr, "lit 309 %ld => %s\n", _x, _status != no_parse ? "yes" : "no");
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "expr 312 @ col %ld?\n", _x);
        assert(cur->expr_id == 0);
        cur->expr_id = 312;
        case 312:
        if (_evaling) {
          struct pacc_mid *_pacc_p;
          PACC_TRACE fprintf(stderr, "312: evaluating\n");
          _pacc_p = cur = _pacc_result(_pacc, _x, 326);
          cur = _pacc_p;
          cur->value.u1=
#line 101 "parse.pacc"
           (rFrom)
#line 2323 "parse.c"
          ;
          PACC_TRACE fprintf(stderr, "stash " TYPE_PRINTF " to (%ld, 326)\n", cur->value.u0, _x);
          goto _pacc_expr_done;
        }
        case 313:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 313 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 324 @ col %ld => %s\n", _x, _status!=no_parse?"yes":"no");
        if (_status != no_parse) {
          PACC_TRACE fprintf(stderr, "accept column registers\n");
          _pacc_Discard(cur->ev_valid); _pacc_Discard(_x);
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "restore column registers\n");
        _pacc_Pop(cur->ev_valid); _pacc_Pop(_x);
        PACC_TRACE fprintf(stderr, "save column registers\n");
        _pacc_Push(_x); _pacc_Push(cur->ev_valid);
        PACC_TRACE fprintf(stderr, "col restored to %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 324 @ col %ld? (next alternative)\n", _x);
        PACC_TRACE fprintf(stderr, "seq 318 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 318;
        _status = parsed;
        PACC_TRACE fprintf(stderr, "lit 314 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "lit 314 @ col %ld => ", _x);
        if (_x+2 <= _pacc->input_length && memcmp(">>", _pacc->string + _x, 2) == 0) {
          _status = parsed;
          _x += 2;
        }
        else {
          _pacc_error(_pacc, ".\">>\"", _x);
          _status = no_parse;
        }
        PACC_TRACE fprintf(stderr, "lit 314 %ld => %s\n", _x, _status != no_parse ? "yes" : "no");
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "expr 317 @ col %ld?\n", _x);
        assert(cur->expr_id == 0);
        cur->expr_id = 317;
        case 317:
        if (_evaling) {
          struct pacc_mid *_pacc_p;
          PACC_TRACE fprintf(stderr, "317: evaluating\n");
          _pacc_p = cur = _pacc_result(_pacc, _x, 326);
          cur = _pacc_p;
          cur->value.u1=
#line 102 "parse.pacc"
            (rAppend)
#line 2374 "parse.c"
          ;
          PACC_TRACE fprintf(stderr, "stash " TYPE_PRINTF " to (%ld, 326)\n", cur->value.u0, _x);
          goto _pacc_expr_done;
        }
        case 318:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 318 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 324 @ col %ld => %s\n", _x, _status!=no_parse?"yes":"no");
        if (_status != no_parse) {
          PACC_TRACE fprintf(stderr, "accept column registers\n");
          _pacc_Discard(cur->ev_valid); _pacc_Discard(_x);
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "restore column registers\n");
        _pacc_Pop(cur->ev_valid); _pacc_Pop(_x);
        PACC_TRACE fprintf(stderr, "save column registers\n");
        _pacc_Push(_x); _pacc_Push(cur->ev_valid);
        PACC_TRACE fprintf(stderr, "col restored to %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 324 @ col %ld? (next alternative)\n", _x);
        PACC_TRACE fprintf(stderr, "seq 323 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 323;
        _status = parsed;
        PACC_TRACE fprintf(stderr, "lit 319 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "lit 319 @ col %ld => ", _x);
        if (_x+1 <= _pacc->input_length && memcmp(">", _pacc->string + _x, 1) == 0) {
          _status = parsed;
          _x += 1;
        }
        else {
          _pacc_error(_pacc, ".\">\"", _x);
          _status = no_parse;
        }
        PACC_TRACE fprintf(stderr, "lit 319 %ld => %s\n", _x, _status != no_parse ? "yes" : "no");
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "expr 322 @ col %ld?\n", _x);
        assert(cur->expr_id == 0);
        cur->expr_id = 322;
        case 322:
        if (_evaling) {
          struct pacc_mid *_pacc_p;
          PACC_TRACE fprintf(stderr, "322: evaluating\n");
          _pacc_p = cur = _pacc_result(_pacc, _x, 326);
          cur = _pacc_p;
          cur->value.u1=
#line 103 "parse.pacc"
           (rCreate)
#line 2425 "parse.c"
          ;
          PACC_TRACE fprintf(stderr, "stash " TYPE_PRINTF " to (%ld, 326)\n", cur->value.u0, _x);
          goto _pacc_expr_done;
        }
        case 323:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 323 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        if (_status == no_parse) {
          PACC_TRACE fprintf(stderr, "restore column registers\n");
          _pacc_Pop(cur->ev_valid); _pacc_Pop(_x);
        }
        else {
          PACC_TRACE fprintf(stderr, "accept column registers\n");
          _pacc_Discard(cur->ev_valid); _pacc_Discard(_x);
        }
        case 324:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "alt 324 @ col %ld => %s\n", _x, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        cur->rule = (cur->rule & ~3) | _status;
        cur->remainder = _x;
        if (_pacc->err_col == _x_rule) {
          _pacc->err_valid = 0;
          _pacc_error(_pacc, ".Redir", _x_rule);
        }
      }
      goto contin;
      case 340: /* Decimal */
      PACC_TRACE fprintf(stderr, "rule 340 (Decimal) col %ld\n", _x);
      _x_rule = _x;
      cur = _pacc_result(_pacc, _x, 340);
      if ((cur->rule & 3) == uncomputed) {
        PACC_TRACE fprintf(stderr, "seq 338 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 338;
        _status = parsed;
        /* bind: d */
        PACC_TRACE fprintf(stderr, "bind 329 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind d @ rule 954, col %ld\n", _x);
        _pacc_save_core(954, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 955;
        _st = 954;
        /* call Decimal:d:0 */
        goto top;
        case 955: /* return from Decimal:d:0 */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 340);
        /* end bind: d */
        if (_status == no_parse) {
          goto contin;
        }
        _pacc_save_core(348, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 330;
        _st = 348;
        /* call _ */
        goto top;
        case 330: /* return from _ */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 340);
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "expr 337 @ col %ld?\n", _x);
        assert(cur->expr_id == 0);
        cur->expr_id = 337;
        case 337:
        if (_evaling) {
          struct pacc_mid *_pacc_p;
          PACC_TRACE fprintf(stderr, "337: evaluating\n");
          _pacc_p = cur = _pacc_result(_pacc, _x, 340);
          cur = _pacc_p;
          cur->value.u2=
#line 105 "parse.pacc"
                              ( atoi((const char *)ref_ptr(ref())) )
#line 2511 "parse.c"
          ;
          PACC_TRACE fprintf(stderr, "stash " TYPE_PRINTF " to (%ld, 340)\n", cur->value.u0, _x);
          goto _pacc_expr_done;
        }
        case 338:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 338 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        cur->rule = (cur->rule & ~3) | _status;
        cur->remainder = _x;
        if (_pacc->err_col == _x_rule) {
          _pacc->err_valid = 0;
          _pacc_error(_pacc, ".Decimal", _x_rule);
        }
      }
      goto contin;
      case 348: /* _ */
      PACC_TRACE fprintf(stderr, "rule 348 (_) col %ld\n", _x);
      _x_rule = _x;
      cur = _pacc_result(_pacc, _x, 348);
      if ((cur->rule & 3) == uncomputed) {
        PACC_TRACE fprintf(stderr, "seq 346 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 346;
        _status = parsed;
        _pacc_save_core(969, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 345;
        _st = 969;
        /* call _:*:0 */
        goto top;
        case 345: /* return from _:*:0 */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 348);
        case 346:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 346 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        cur->rule = (cur->rule & ~3) | _status;
        cur->remainder = _x;
        if (_pacc->err_col == _x_rule) {
          _pacc->err_valid = 0;
          _pacc_error(_pacc, "._", _x_rule);
        }
      }
      goto contin;
      case 373: /* case */
      PACC_TRACE fprintf(stderr, "rule 373 (case) col %ld\n", _x);
      _x_rule = _x;
      cur = _pacc_result(_pacc, _x, 373);
      if ((cur->rule & 3) == uncomputed) {
        PACC_TRACE fprintf(stderr, "alt 371 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 371;
        PACC_TRACE fprintf(stderr, "save column registers\n");
        _pacc_Push(_x); _pacc_Push(cur->ev_valid);
        PACC_TRACE fprintf(stderr, "seq 359 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 359;
        _status = parsed;
        PACC_TRACE fprintf(stderr, "seq 350 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 350;
        _status = parsed;
        /* bind: _pacc_bl350 */
        PACC_TRACE fprintf(stderr, "bind 920 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind _pacc_bl350 @ rule 885, col %ld\n", _x);
        _pacc_save_core(885, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 349;
        _st = 885;
        /* call Word */
        goto top;
        case 349: /* return from Word */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 373);
        /* end bind: _pacc_bl350 */
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "guard 919 @ col %ld?\n", _x);
        /* 919: guard_pre() */
           {
          struct pacc_mid *_pacc_p;
          /* i is 0, type is ref_t */
          ref_t _pacc_bl350;
          _pacc_p = cur; _evaling = 1;
          _pos = 0;
          PACC_TRACE fprintf(stderr, "binding of _pacc_bl350: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind _pacc_bl350 to r885 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 885);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 918;
            _pacc_ev_i = 0; goto eval_loop;
            case 918:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          _pacc_bl350 = cur->value.u4;
          PACC_TRACE fprintf(stderr, "bound _pacc_bl350 to r885 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          cur = _pacc_p; _evaling = 0;
          _status = (
(ref_streq(_pacc_bl350,"case"))
#line 2623 "parse.c"
          ) ? parsed : no_parse;
          PACC_TRACE fprintf(stderr, "guard 919 %ld => %s\n", _x, _status != no_parse ? "yes" : "no");
        }
        case 350:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 350 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        if (_status == no_parse) {
          goto contin;
        }
        /* bind: w */
        PACC_TRACE fprintf(stderr, "bind 352 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind w @ rule 843, col %ld\n", _x);
        _pacc_save_core(843, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 351;
        _st = 843;
        /* call Words */
        goto top;
        case 351: /* return from Words */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 373);
        /* end bind: w */
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "lit 353 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "lit 353 @ col %ld => ", _x);
        if (_x+1 <= _pacc->input_length && memcmp(";", _pacc->string + _x, 1) == 0) {
          _status = parsed;
          _x += 1;
        }
        else {
          _pacc_error(_pacc, ".\";\"", _x);
          _status = no_parse;
        }
        PACC_TRACE fprintf(stderr, "lit 353 %ld => %s\n", _x, _status != no_parse ? "yes" : "no");
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "expr 358 @ col %ld?\n", _x);
        assert(cur->expr_id == 0);
        cur->expr_id = 358;
        case 358:
        if (_evaling) {
          struct pacc_mid *_pacc_p;
          /* i is 0, type is struct Node * */
          struct Node * w;
          PACC_TRACE fprintf(stderr, "358: evaluating\n");
          _pacc_p = cur = _pacc_result(_pacc, _x, 373);
          _pos = 0;
          PACC_TRACE fprintf(stderr, "binding of w: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind w to r843 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 843);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 354;
            _pacc_ev_i = 0; goto eval_loop;
            case 354:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          w = cur->value.u3;
          PACC_TRACE fprintf(stderr, "bound w to r843 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          cur = _pacc_p;
          cur->value.u3=
#line 109 "parse.pacc"
                                                 ( mk(nCase, w) )
#line 2695 "parse.c"
          ;
          PACC_TRACE fprintf(stderr, "stash " TYPE_PRINTF " to (%ld, 373)\n", cur->value.u0, _x);
          goto _pacc_expr_done;
        }
        case 359:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 359 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 371 @ col %ld => %s\n", _x, _status!=no_parse?"yes":"no");
        if (_status != no_parse) {
          PACC_TRACE fprintf(stderr, "accept column registers\n");
          _pacc_Discard(cur->ev_valid); _pacc_Discard(_x);
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "restore column registers\n");
        _pacc_Pop(cur->ev_valid); _pacc_Pop(_x);
        PACC_TRACE fprintf(stderr, "save column registers\n");
        _pacc_Push(_x); _pacc_Push(cur->ev_valid);
        PACC_TRACE fprintf(stderr, "col restored to %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 371 @ col %ld? (next alternative)\n", _x);
        PACC_TRACE fprintf(stderr, "seq 370 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 370;
        _status = parsed;
        PACC_TRACE fprintf(stderr, "seq 361 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 361;
        _status = parsed;
        /* bind: _pacc_bl361 */
        PACC_TRACE fprintf(stderr, "bind 923 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind _pacc_bl361 @ rule 885, col %ld\n", _x);
        _pacc_save_core(885, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 360;
        _st = 885;
        /* call Word */
        goto top;
        case 360: /* return from Word */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 373);
        /* end bind: _pacc_bl361 */
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "guard 922 @ col %ld?\n", _x);
        /* 922: guard_pre() */
           {
          struct pacc_mid *_pacc_p;
          /* i is 0, type is ref_t */
          ref_t _pacc_bl361;
          _pacc_p = cur; _evaling = 1;
          _pos = 0;
          PACC_TRACE fprintf(stderr, "binding of _pacc_bl361: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind _pacc_bl361 to r885 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 885);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 921;
            _pacc_ev_i = 0; goto eval_loop;
            case 921:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          _pacc_bl361 = cur->value.u4;
          PACC_TRACE fprintf(stderr, "bound _pacc_bl361 to r885 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          cur = _pacc_p; _evaling = 0;
          _status = (
(ref_streq(_pacc_bl361,"case"))
#line 2767 "parse.c"
          ) ? parsed : no_parse;
          PACC_TRACE fprintf(stderr, "guard 922 %ld => %s\n", _x, _status != no_parse ? "yes" : "no");
        }
        case 361:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 361 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        if (_status == no_parse) {
          goto contin;
        }
        /* bind: w */
        PACC_TRACE fprintf(stderr, "bind 363 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind w @ rule 843, col %ld\n", _x);
        _pacc_save_core(843, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 362;
        _st = 843;
        /* call Words */
        goto top;
        case 362: /* return from Words */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 373);
        /* end bind: w */
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "lit 364 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "lit 364 @ col %ld => ", _x);
        if (_x+1 <= _pacc->input_length && memcmp("\n", _pacc->string + _x, 1) == 0) {
          _status = parsed;
          _x += 1;
        }
        else {
          _pacc_error(_pacc, ".\"\n\"", _x);
          _status = no_parse;
        }
        PACC_TRACE fprintf(stderr, "lit 364 %ld => %s\n", _x, _status != no_parse ? "yes" : "no");
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "expr 369 @ col %ld?\n", _x);
        assert(cur->expr_id == 0);
        cur->expr_id = 369;
        case 369:
        if (_evaling) {
          struct pacc_mid *_pacc_p;
          /* i is 0, type is struct Node * */
          struct Node * w;
          PACC_TRACE fprintf(stderr, "369: evaluating\n");
          _pacc_p = cur = _pacc_result(_pacc, _x, 373);
          _pos = 0;
          PACC_TRACE fprintf(stderr, "binding of w: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind w to r843 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 843);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 365;
            _pacc_ev_i = 0; goto eval_loop;
            case 365:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          w = cur->value.u3;
          PACC_TRACE fprintf(stderr, "bound w to r843 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          cur = _pacc_p;
          cur->value.u3=
#line 110 "parse.pacc"
                               ( mk(nCase, w) )
#line 2839 "parse.c"
          ;
          PACC_TRACE fprintf(stderr, "stash " TYPE_PRINTF " to (%ld, 373)\n", cur->value.u0, _x);
          goto _pacc_expr_done;
        }
        case 370:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 370 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        if (_status == no_parse) {
          PACC_TRACE fprintf(stderr, "restore column registers\n");
          _pacc_Pop(cur->ev_valid); _pacc_Pop(_x);
        }
        else {
          PACC_TRACE fprintf(stderr, "accept column registers\n");
          _pacc_Discard(cur->ev_valid); _pacc_Discard(_x);
        }
        case 371:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "alt 371 @ col %ld => %s\n", _x, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        cur->rule = (cur->rule & ~3) | _status;
        cur->remainder = _x;
        if (_pacc->err_col == _x_rule) {
          _pacc->err_valid = 0;
          _pacc_error(_pacc, ".case", _x_rule);
        }
      }
      goto contin;
      case 407: /* cbody */
      PACC_TRACE fprintf(stderr, "rule 407 (cbody) col %ld\n", _x);
      _x_rule = _x;
      cur = _pacc_result(_pacc, _x, 407);
      if ((cur->rule & 3) == uncomputed) {
        PACC_TRACE fprintf(stderr, "alt 405 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 405;
        PACC_TRACE fprintf(stderr, "save column registers\n");
        _pacc_Push(_x); _pacc_Push(cur->ev_valid);
        PACC_TRACE fprintf(stderr, "seq 382 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 382;
        _status = parsed;
        /* bind: c */
        PACC_TRACE fprintf(stderr, "bind 375 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind c @ rule 621, col %ld\n", _x);
        _pacc_save_core(621, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 374;
        _st = 621;
        /* call cmd */
        goto top;
        case 374: /* return from cmd */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 407);
        /* end bind: c */
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "expr 381 @ col %ld?\n", _x);
        assert(cur->expr_id == 0);
        cur->expr_id = 381;
        case 381:
        if (_evaling) {
          struct pacc_mid *_pacc_p;
          /* i is 0, type is struct Node * */
          struct Node * c;
          PACC_TRACE fprintf(stderr, "381: evaluating\n");
          _pacc_p = cur = _pacc_result(_pacc, _x, 407);
          _pos = 0;
          PACC_TRACE fprintf(stderr, "binding of c: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind c to r621 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 621);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 377;
            _pacc_ev_i = 0; goto eval_loop;
            case 377:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          c = cur->value.u3;
          PACC_TRACE fprintf(stderr, "bound c to r621 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          cur = _pacc_p;
          cur->value.u3=
#line 112 "parse.pacc"
                  ( mk(nCbody, c, NULL) )
#line 2929 "parse.c"
          ;
          PACC_TRACE fprintf(stderr, "stash " TYPE_PRINTF " to (%ld, 407)\n", cur->value.u0, _x);
          goto _pacc_expr_done;
        }
        case 382:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 382 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 405 @ col %ld => %s\n", _x, _status!=no_parse?"yes":"no");
        if (_status != no_parse) {
          PACC_TRACE fprintf(stderr, "accept column registers\n");
          _pacc_Discard(cur->ev_valid); _pacc_Discard(_x);
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "restore column registers\n");
        _pacc_Pop(cur->ev_valid); _pacc_Pop(_x);
        PACC_TRACE fprintf(stderr, "save column registers\n");
        _pacc_Push(_x); _pacc_Push(cur->ev_valid);
        PACC_TRACE fprintf(stderr, "col restored to %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 405 @ col %ld? (next alternative)\n", _x);
        PACC_TRACE fprintf(stderr, "seq 393 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 393;
        _status = parsed;
        /* bind: c */
        PACC_TRACE fprintf(stderr, "bind 384 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind c @ rule 373, col %ld\n", _x);
        _pacc_save_core(373, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 383;
        _st = 373;
        /* call case */
        goto top;
        case 383: /* return from case */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 407);
        /* end bind: c */
        if (_status == no_parse) {
          goto contin;
        }
        /* bind: d */
        PACC_TRACE fprintf(stderr, "bind 386 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind d @ rule 407, col %ld\n", _x);
        _pacc_save_core(407, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 385;
        _st = 407;
        /* call cbody */
        goto top;
        case 385: /* return from cbody */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 407);
        /* end bind: d */
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "expr 392 @ col %ld?\n", _x);
        assert(cur->expr_id == 0);
        cur->expr_id = 392;
        case 392:
        if (_evaling) {
          struct pacc_mid *_pacc_p;
          /* i is 0, type is struct Node * */
          struct Node * c;
          /* i is 1, type is struct Node * */
          struct Node * d;
          PACC_TRACE fprintf(stderr, "392: evaluating\n");
          _pacc_p = cur = _pacc_result(_pacc, _x, 407);
          _pos = 0;
          PACC_TRACE fprintf(stderr, "binding of c: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind c to r373 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 373);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 388;
            _pacc_ev_i = 0; goto eval_loop;
            case 388:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          c = cur->value.u3;
          PACC_TRACE fprintf(stderr, "bound c to r373 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          _pos = 1;
          PACC_TRACE fprintf(stderr, "binding of d: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind d to r407 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 407);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 387;
            _pacc_ev_i = 0; goto eval_loop;
            case 387:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          d = cur->value.u3;
          PACC_TRACE fprintf(stderr, "bound d to r407 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          cur = _pacc_p;
          cur->value.u3=
#line 113 "parse.pacc"
                    ( mk(nCbody, c, d) )
#line 3036 "parse.c"
          ;
          PACC_TRACE fprintf(stderr, "stash " TYPE_PRINTF " to (%ld, 407)\n", cur->value.u0, _x);
          goto _pacc_expr_done;
        }
        case 393:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 393 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 405 @ col %ld => %s\n", _x, _status!=no_parse?"yes":"no");
        if (_status != no_parse) {
          PACC_TRACE fprintf(stderr, "accept column registers\n");
          _pacc_Discard(cur->ev_valid); _pacc_Discard(_x);
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "restore column registers\n");
        _pacc_Pop(cur->ev_valid); _pacc_Pop(_x);
        PACC_TRACE fprintf(stderr, "save column registers\n");
        _pacc_Push(_x); _pacc_Push(cur->ev_valid);
        PACC_TRACE fprintf(stderr, "col restored to %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 405 @ col %ld? (next alternative)\n", _x);
        PACC_TRACE fprintf(stderr, "seq 404 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 404;
        _status = parsed;
        /* bind: c */
        PACC_TRACE fprintf(stderr, "bind 395 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind c @ rule 211, col %ld\n", _x);
        _pacc_save_core(211, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 394;
        _st = 211;
        /* call cmdsan */
        goto top;
        case 394: /* return from cmdsan */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 407);
        /* end bind: c */
        if (_status == no_parse) {
          goto contin;
        }
        /* bind: d */
        PACC_TRACE fprintf(stderr, "bind 397 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind d @ rule 407, col %ld\n", _x);
        _pacc_save_core(407, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 396;
        _st = 407;
        /* call cbody */
        goto top;
        case 396: /* return from cbody */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 407);
        /* end bind: d */
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "expr 403 @ col %ld?\n", _x);
        assert(cur->expr_id == 0);
        cur->expr_id = 403;
        case 403:
        if (_evaling) {
          struct pacc_mid *_pacc_p;
          /* i is 0, type is Node * */
          Node * c;
          /* i is 1, type is struct Node * */
          struct Node * d;
          PACC_TRACE fprintf(stderr, "403: evaluating\n");
          _pacc_p = cur = _pacc_result(_pacc, _x, 407);
          _pos = 0;
          PACC_TRACE fprintf(stderr, "binding of c: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind c to r211 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 211);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 399;
            _pacc_ev_i = 0; goto eval_loop;
            case 399:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          c = cur->value.u0;
          PACC_TRACE fprintf(stderr, "bound c to r211 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          _pos = 1;
          PACC_TRACE fprintf(stderr, "binding of d: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind d to r407 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 407);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 398;
            _pacc_ev_i = 0; goto eval_loop;
            case 398:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          d = cur->value.u3;
          PACC_TRACE fprintf(stderr, "bound d to r407 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          cur = _pacc_p;
          cur->value.u3=
#line 114 "parse.pacc"
                      ( mk(nCbody, c, d) )
#line 3143 "parse.c"
          ;
          PACC_TRACE fprintf(stderr, "stash " TYPE_PRINTF " to (%ld, 407)\n", cur->value.u0, _x);
          goto _pacc_expr_done;
        }
        case 404:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 404 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        if (_status == no_parse) {
          PACC_TRACE fprintf(stderr, "restore column registers\n");
          _pacc_Pop(cur->ev_valid); _pacc_Pop(_x);
        }
        else {
          PACC_TRACE fprintf(stderr, "accept column registers\n");
          _pacc_Discard(cur->ev_valid); _pacc_Discard(_x);
        }
        case 405:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "alt 405 @ col %ld => %s\n", _x, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        cur->rule = (cur->rule & ~3) | _status;
        cur->remainder = _x;
        if (_pacc->err_col == _x_rule) {
          _pacc->err_valid = 0;
          _pacc_error(_pacc, ".cbody", _x_rule);
        }
      }
      goto contin;
      case 430: /* iftail */
      PACC_TRACE fprintf(stderr, "rule 430 (iftail) col %ld\n", _x);
      _x_rule = _x;
      cur = _pacc_result(_pacc, _x, 430);
      if ((cur->rule & 3) == uncomputed) {
        PACC_TRACE fprintf(stderr, "alt 428 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 428;
        PACC_TRACE fprintf(stderr, "save column registers\n");
        _pacc_Push(_x); _pacc_Push(cur->ev_valid);
        PACC_TRACE fprintf(stderr, "seq 413 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 413;
        _status = parsed;
        /* bind: c */
        PACC_TRACE fprintf(stderr, "bind 409 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind c @ rule 621, col %ld\n", _x);
        _pacc_save_core(621, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 408;
        _st = 621;
        /* call cmd */
        goto top;
        case 408: /* return from cmd */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 430);
        /* end bind: c */
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "expr 412 @ col %ld?\n", _x);
        assert(cur->expr_id == 0);
        cur->expr_id = 412;
        case 412:
        if (_evaling) {
          struct pacc_mid *_pacc_p;
          /* i is 0, type is struct Node * */
          struct Node * c;
          PACC_TRACE fprintf(stderr, "412: evaluating\n");
          _pacc_p = cur = _pacc_result(_pacc, _x, 430);
          _pos = 0;
          PACC_TRACE fprintf(stderr, "binding of c: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind c to r621 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 621);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 410;
            _pacc_ev_i = 0; goto eval_loop;
            case 410:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          c = cur->value.u3;
          PACC_TRACE fprintf(stderr, "bound c to r621 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          cur = _pacc_p;
          cur->value.u3=
#line 116 "parse.pacc"
                (c)
#line 3233 "parse.c"
          ;
          PACC_TRACE fprintf(stderr, "stash " TYPE_PRINTF " to (%ld, 430)\n", cur->value.u0, _x);
          goto _pacc_expr_done;
        }
        case 413:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 413 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 428 @ col %ld => %s\n", _x, _status!=no_parse?"yes":"no");
        if (_status != no_parse) {
          PACC_TRACE fprintf(stderr, "accept column registers\n");
          _pacc_Discard(cur->ev_valid); _pacc_Discard(_x);
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "restore column registers\n");
        _pacc_Pop(cur->ev_valid); _pacc_Pop(_x);
        PACC_TRACE fprintf(stderr, "save column registers\n");
        _pacc_Push(_x); _pacc_Push(cur->ev_valid);
        PACC_TRACE fprintf(stderr, "col restored to %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 428 @ col %ld? (next alternative)\n", _x);
        PACC_TRACE fprintf(stderr, "seq 427 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 427;
        _status = parsed;
        /* bind: b */
        PACC_TRACE fprintf(stderr, "bind 415 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind b @ rule 221, col %ld\n", _x);
        _pacc_save_core(221, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 414;
        _st = 221;
        /* call brace */
        goto top;
        case 414: /* return from brace */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 430);
        /* end bind: b */
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "seq 417 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 417;
        _status = parsed;
        /* bind: _pacc_bl417 */
        PACC_TRACE fprintf(stderr, "bind 926 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind _pacc_bl417 @ rule 885, col %ld\n", _x);
        _pacc_save_core(885, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 416;
        _st = 885;
        /* call Word */
        goto top;
        case 416: /* return from Word */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 430);
        /* end bind: _pacc_bl417 */
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "guard 925 @ col %ld?\n", _x);
        /* 925: guard_pre() */
           {
          struct pacc_mid *_pacc_p;
          /* i is 1, type is ref_t */
          ref_t _pacc_bl417;
          _pacc_p = cur; _evaling = 1;
          _pos = 1;
          PACC_TRACE fprintf(stderr, "binding of _pacc_bl417: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind _pacc_bl417 to r885 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 885);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 924;
            _pacc_ev_i = 0; goto eval_loop;
            case 924:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          _pacc_bl417 = cur->value.u4;
          PACC_TRACE fprintf(stderr, "bound _pacc_bl417 to r885 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          cur = _pacc_p; _evaling = 0;
          _status = (
(ref_streq(_pacc_bl417,"else"))
#line 3325 "parse.c"
          ) ? parsed : no_parse;
          PACC_TRACE fprintf(stderr, "guard 925 %ld => %s\n", _x, _status != no_parse ? "yes" : "no");
        }
        case 417:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 417 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        if (_status == no_parse) {
          goto contin;
        }
        _pacc_save_core(906, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 418;
        _st = 906;
        /* call optNl */
        goto top;
        case 418: /* return from optNl */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 430);
        if (_status == no_parse) {
          goto contin;
        }
        /* bind: c */
        PACC_TRACE fprintf(stderr, "bind 420 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind c @ rule 621, col %ld\n", _x);
        _pacc_save_core(621, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 419;
        _st = 621;
        /* call cmd */
        goto top;
        case 419: /* return from cmd */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 430);
        /* end bind: c */
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "expr 426 @ col %ld?\n", _x);
        assert(cur->expr_id == 0);
        cur->expr_id = 426;
        case 426:
        if (_evaling) {
          struct pacc_mid *_pacc_p;
          /* i is 0, type is Node * */
          Node * b;
          /* i is 2, type is struct Node * */
          struct Node * c;
          PACC_TRACE fprintf(stderr, "426: evaluating\n");
          _pacc_p = cur = _pacc_result(_pacc, _x, 430);
          _pos = 0;
          PACC_TRACE fprintf(stderr, "binding of b: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind b to r221 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 221);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 422;
            _pacc_ev_i = 0; goto eval_loop;
            case 422:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          b = cur->value.u0;
          PACC_TRACE fprintf(stderr, "bound b to r221 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          _pos = 2;
          PACC_TRACE fprintf(stderr, "binding of c: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind c to r621 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 621);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 421;
            _pacc_ev_i = 0; goto eval_loop;
            case 421:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          c = cur->value.u3;
          PACC_TRACE fprintf(stderr, "bound c to r621 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          cur = _pacc_p;
          cur->value.u3=
#line 117 "parse.pacc"
                                   ( mk(nElse, b, c) )
#line 3414 "parse.c"
          ;
          PACC_TRACE fprintf(stderr, "stash " TYPE_PRINTF " to (%ld, 430)\n", cur->value.u0, _x);
          goto _pacc_expr_done;
        }
        case 427:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 427 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        if (_status == no_parse) {
          PACC_TRACE fprintf(stderr, "restore column registers\n");
          _pacc_Pop(cur->ev_valid); _pacc_Pop(_x);
        }
        else {
          PACC_TRACE fprintf(stderr, "accept column registers\n");
          _pacc_Discard(cur->ev_valid); _pacc_Discard(_x);
        }
        case 428:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "alt 428 @ col %ld => %s\n", _x, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        cur->rule = (cur->rule & ~3) | _status;
        cur->remainder = _x;
        if (_pacc->err_col == _x_rule) {
          _pacc->err_valid = 0;
          _pacc_error(_pacc, ".iftail", _x_rule);
        }
      }
      goto contin;
      case 621: /* cmd */
      PACC_TRACE fprintf(stderr, "rule 621 (cmd) col %ld\n", _x);
      _x_rule = _x;
      cur = _pacc_result(_pacc, _x, 621);
      if ((cur->rule & 3) == uncomputed) {
        PACC_TRACE fprintf(stderr, "alt 619 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 619;
        PACC_TRACE fprintf(stderr, "save column registers\n");
        _pacc_Push(_x); _pacc_Push(cur->ev_valid);
        PACC_TRACE fprintf(stderr, "seq 433 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 433;
        _status = parsed;
        PACC_TRACE fprintf(stderr, "expr 432 @ col %ld?\n", _x);
        assert(cur->expr_id == 0);
        cur->expr_id = 432;
        case 432:
        if (_evaling) {
          struct pacc_mid *_pacc_p;
          PACC_TRACE fprintf(stderr, "432: evaluating\n");
          _pacc_p = cur = _pacc_result(_pacc, _x, 621);
          cur = _pacc_p;
          cur->value.u3=
#line 119 "parse.pacc"
         (0)
#line 3469 "parse.c"
          ;
          PACC_TRACE fprintf(stderr, "stash " TYPE_PRINTF " to (%ld, 621)\n", cur->value.u0, _x);
          goto _pacc_expr_done;
        }
        case 433:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 433 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 619 @ col %ld => %s\n", _x, _status!=no_parse?"yes":"no");
        if (_status != no_parse) {
          PACC_TRACE fprintf(stderr, "accept column registers\n");
          _pacc_Discard(cur->ev_valid); _pacc_Discard(_x);
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "restore column registers\n");
        _pacc_Pop(cur->ev_valid); _pacc_Pop(_x);
        PACC_TRACE fprintf(stderr, "save column registers\n");
        _pacc_Push(_x); _pacc_Push(cur->ev_valid);
        PACC_TRACE fprintf(stderr, "col restored to %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 619 @ col %ld? (next alternative)\n", _x);
        PACC_TRACE fprintf(stderr, "seq 439 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 439;
        _status = parsed;
        /* bind: s */
        PACC_TRACE fprintf(stderr, "bind 435 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind s @ rule 634, col %ld\n", _x);
        _pacc_save_core(634, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 434;
        _st = 634;
        /* call SimpleRedir */
        goto top;
        case 434: /* return from SimpleRedir */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 621);
        /* end bind: s */
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "expr 438 @ col %ld?\n", _x);
        assert(cur->expr_id == 0);
        cur->expr_id = 438;
        case 438:
        if (_evaling) {
          struct pacc_mid *_pacc_p;
          /* i is 0, type is struct Node * */
          struct Node * s;
          PACC_TRACE fprintf(stderr, "438: evaluating\n");
          _pacc_p = cur = _pacc_result(_pacc, _x, 621);
          _pos = 0;
          PACC_TRACE fprintf(stderr, "binding of s: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind s to r634 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 634);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 436;
            _pacc_ev_i = 0; goto eval_loop;
            case 436:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          s = cur->value.u3;
          PACC_TRACE fprintf(stderr, "bound s to r634 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          cur = _pacc_p;
          cur->value.u3=
#line 120 "parse.pacc"
                  (s)
#line 3541 "parse.c"
          ;
          PACC_TRACE fprintf(stderr, "stash " TYPE_PRINTF " to (%ld, 621)\n", cur->value.u0, _x);
          goto _pacc_expr_done;
        }
        case 439:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 439 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 619 @ col %ld => %s\n", _x, _status!=no_parse?"yes":"no");
        if (_status != no_parse) {
          PACC_TRACE fprintf(stderr, "accept column registers\n");
          _pacc_Discard(cur->ev_valid); _pacc_Discard(_x);
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "restore column registers\n");
        _pacc_Pop(cur->ev_valid); _pacc_Pop(_x);
        PACC_TRACE fprintf(stderr, "save column registers\n");
        _pacc_Push(_x); _pacc_Push(cur->ev_valid);
        PACC_TRACE fprintf(stderr, "col restored to %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 619 @ col %ld? (next alternative)\n", _x);
        PACC_TRACE fprintf(stderr, "seq 450 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 450;
        _status = parsed;
        /* bind: b */
        PACC_TRACE fprintf(stderr, "bind 441 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind b @ rule 221, col %ld\n", _x);
        _pacc_save_core(221, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 440;
        _st = 221;
        /* call brace */
        goto top;
        case 440: /* return from brace */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 621);
        /* end bind: b */
        if (_status == no_parse) {
          goto contin;
        }
        /* bind: e */
        PACC_TRACE fprintf(stderr, "bind 443 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind e @ rule 262, col %ld\n", _x);
        _pacc_save_core(262, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 442;
        _st = 262;
        /* call epilog */
        goto top;
        case 442: /* return from epilog */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 621);
        /* end bind: e */
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "expr 449 @ col %ld?\n", _x);
        assert(cur->expr_id == 0);
        cur->expr_id = 449;
        case 449:
        if (_evaling) {
          struct pacc_mid *_pacc_p;
          /* i is 0, type is Node * */
          Node * b;
          /* i is 1, type is Node * */
          Node * e;
          PACC_TRACE fprintf(stderr, "449: evaluating\n");
          _pacc_p = cur = _pacc_result(_pacc, _x, 621);
          _pos = 0;
          PACC_TRACE fprintf(stderr, "binding of b: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind b to r221 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 221);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 445;
            _pacc_ev_i = 0; goto eval_loop;
            case 445:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          b = cur->value.u0;
          PACC_TRACE fprintf(stderr, "bound b to r221 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          _pos = 1;
          PACC_TRACE fprintf(stderr, "binding of e: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind e to r262 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 262);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 444;
            _pacc_ev_i = 0; goto eval_loop;
            case 444:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          e = cur->value.u0;
          PACC_TRACE fprintf(stderr, "bound e to r262 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          cur = _pacc_p;
          cur->value.u3=
#line 121 "parse.pacc"
                      ( mk(nBrace, b, e) )
#line 3648 "parse.c"
          ;
          PACC_TRACE fprintf(stderr, "stash " TYPE_PRINTF " to (%ld, 621)\n", cur->value.u0, _x);
          goto _pacc_expr_done;
        }
        case 450:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 450 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 619 @ col %ld => %s\n", _x, _status!=no_parse?"yes":"no");
        if (_status != no_parse) {
          PACC_TRACE fprintf(stderr, "accept column registers\n");
          _pacc_Discard(cur->ev_valid); _pacc_Discard(_x);
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "restore column registers\n");
        _pacc_Pop(cur->ev_valid); _pacc_Pop(_x);
        PACC_TRACE fprintf(stderr, "save column registers\n");
        _pacc_Push(_x); _pacc_Push(cur->ev_valid);
        PACC_TRACE fprintf(stderr, "col restored to %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 619 @ col %ld? (next alternative)\n", _x);
        PACC_TRACE fprintf(stderr, "seq 464 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 464;
        _status = parsed;
        PACC_TRACE fprintf(stderr, "seq 452 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 452;
        _status = parsed;
        /* bind: _pacc_bl452 */
        PACC_TRACE fprintf(stderr, "bind 929 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind _pacc_bl452 @ rule 885, col %ld\n", _x);
        _pacc_save_core(885, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 451;
        _st = 885;
        /* call Word */
        goto top;
        case 451: /* return from Word */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 621);
        /* end bind: _pacc_bl452 */
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "guard 928 @ col %ld?\n", _x);
        /* 928: guard_pre() */
           {
          struct pacc_mid *_pacc_p;
          /* i is 0, type is ref_t */
          ref_t _pacc_bl452;
          _pacc_p = cur; _evaling = 1;
          _pos = 0;
          PACC_TRACE fprintf(stderr, "binding of _pacc_bl452: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind _pacc_bl452 to r885 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 885);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 927;
            _pacc_ev_i = 0; goto eval_loop;
            case 927:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          _pacc_bl452 = cur->value.u4;
          PACC_TRACE fprintf(stderr, "bound _pacc_bl452 to r885 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          cur = _pacc_p; _evaling = 0;
          _status = (
(ref_streq(_pacc_bl452,"if"))
#line 3720 "parse.c"
          ) ? parsed : no_parse;
          PACC_TRACE fprintf(stderr, "guard 928 %ld => %s\n", _x, _status != no_parse ? "yes" : "no");
        }
        case 452:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 452 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        if (_status == no_parse) {
          goto contin;
        }
        /* bind: p */
        PACC_TRACE fprintf(stderr, "bind 454 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind p @ rule 231, col %ld\n", _x);
        _pacc_save_core(231, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 453;
        _st = 231;
        /* call paren */
        goto top;
        case 453: /* return from paren */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 621);
        /* end bind: p */
        if (_status == no_parse) {
          goto contin;
        }
        _pacc_save_core(906, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 455;
        _st = 906;
        /* call optNl */
        goto top;
        case 455: /* return from optNl */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 621);
        if (_status == no_parse) {
          goto contin;
        }
        /* bind: t */
        PACC_TRACE fprintf(stderr, "bind 457 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind t @ rule 430, col %ld\n", _x);
        _pacc_save_core(430, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 456;
        _st = 430;
        /* call iftail */
        goto top;
        case 456: /* return from iftail */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 621);
        /* end bind: t */
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "expr 463 @ col %ld?\n", _x);
        assert(cur->expr_id == 0);
        cur->expr_id = 463;
        case 463:
        if (_evaling) {
          struct pacc_mid *_pacc_p;
          /* i is 0, type is Node * */
          Node * p;
          /* i is 2, type is struct Node * */
          struct Node * t;
          PACC_TRACE fprintf(stderr, "463: evaluating\n");
          _pacc_p = cur = _pacc_result(_pacc, _x, 621);
          _pos = 0;
          PACC_TRACE fprintf(stderr, "binding of p: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind p to r231 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 231);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 459;
            _pacc_ev_i = 0; goto eval_loop;
            case 459:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          p = cur->value.u0;
          PACC_TRACE fprintf(stderr, "bound p to r231 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          _pos = 2;
          PACC_TRACE fprintf(stderr, "binding of t: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind t to r430 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 430);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 458;
            _pacc_ev_i = 0; goto eval_loop;
            case 458:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          t = cur->value.u3;
          PACC_TRACE fprintf(stderr, "bound t to r430 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          cur = _pacc_p;
          cur->value.u3=
#line 122 "parse.pacc"
                                    ( mk(nIf, p, t) )
#line 3829 "parse.c"
          ;
          PACC_TRACE fprintf(stderr, "stash " TYPE_PRINTF " to (%ld, 621)\n", cur->value.u0, _x);
          goto _pacc_expr_done;
        }
        case 464:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 464 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 619 @ col %ld => %s\n", _x, _status!=no_parse?"yes":"no");
        if (_status != no_parse) {
          PACC_TRACE fprintf(stderr, "accept column registers\n");
          _pacc_Discard(cur->ev_valid); _pacc_Discard(_x);
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "restore column registers\n");
        _pacc_Pop(cur->ev_valid); _pacc_Pop(_x);
        PACC_TRACE fprintf(stderr, "save column registers\n");
        _pacc_Push(_x); _pacc_Push(cur->ev_valid);
        PACC_TRACE fprintf(stderr, "col restored to %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 619 @ col %ld? (next alternative)\n", _x);
        PACC_TRACE fprintf(stderr, "seq 485 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 485;
        _status = parsed;
        PACC_TRACE fprintf(stderr, "seq 466 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 466;
        _status = parsed;
        /* bind: _pacc_bl466 */
        PACC_TRACE fprintf(stderr, "bind 932 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind _pacc_bl466 @ rule 885, col %ld\n", _x);
        _pacc_save_core(885, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 465;
        _st = 885;
        /* call Word */
        goto top;
        case 465: /* return from Word */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 621);
        /* end bind: _pacc_bl466 */
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "guard 931 @ col %ld?\n", _x);
        /* 931: guard_pre() */
           {
          struct pacc_mid *_pacc_p;
          /* i is 0, type is ref_t */
          ref_t _pacc_bl466;
          _pacc_p = cur; _evaling = 1;
          _pos = 0;
          PACC_TRACE fprintf(stderr, "binding of _pacc_bl466: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind _pacc_bl466 to r885 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 885);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 930;
            _pacc_ev_i = 0; goto eval_loop;
            case 930:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          _pacc_bl466 = cur->value.u4;
          PACC_TRACE fprintf(stderr, "bound _pacc_bl466 to r885 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          cur = _pacc_p; _evaling = 0;
          _status = (
(ref_streq(_pacc_bl466,"for"))
#line 3901 "parse.c"
          ) ? parsed : no_parse;
          PACC_TRACE fprintf(stderr, "guard 931 %ld => %s\n", _x, _status != no_parse ? "yes" : "no");
        }
        case 466:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 466 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "lit 467 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "lit 467 @ col %ld => ", _x);
        if (_x+1 <= _pacc->input_length && memcmp("(", _pacc->string + _x, 1) == 0) {
          _status = parsed;
          _x += 1;
        }
        else {
          _pacc_error(_pacc, ".\"(\"", _x);
          _status = no_parse;
        }
        PACC_TRACE fprintf(stderr, "lit 467 %ld => %s\n", _x, _status != no_parse ? "yes" : "no");
        if (_status == no_parse) {
          goto contin;
        }
        /* bind: w */
        PACC_TRACE fprintf(stderr, "bind 469 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind w @ rule 695, col %ld\n", _x);
        _pacc_save_core(695, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 468;
        _st = 695;
        /* call word */
        goto top;
        case 468: /* return from word */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 621);
        /* end bind: w */
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "seq 471 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 471;
        _status = parsed;
        /* bind: _pacc_bl471 */
        PACC_TRACE fprintf(stderr, "bind 935 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind _pacc_bl471 @ rule 885, col %ld\n", _x);
        _pacc_save_core(885, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 470;
        _st = 885;
        /* call Word */
        goto top;
        case 470: /* return from Word */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 621);
        /* end bind: _pacc_bl471 */
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "guard 934 @ col %ld?\n", _x);
        /* 934: guard_pre() */
           {
          struct pacc_mid *_pacc_p;
          /* i is 1, type is ref_t */
          ref_t _pacc_bl471;
          _pacc_p = cur; _evaling = 1;
          _pos = 1;
          PACC_TRACE fprintf(stderr, "binding of _pacc_bl471: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind _pacc_bl471 to r885 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 885);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 933;
            _pacc_ev_i = 0; goto eval_loop;
            case 933:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          _pacc_bl471 = cur->value.u4;
          PACC_TRACE fprintf(stderr, "bound _pacc_bl471 to r885 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          cur = _pacc_p; _evaling = 0;
          _status = (
(ref_streq(_pacc_bl471,"in"))
#line 3993 "parse.c"
          ) ? parsed : no_parse;
          PACC_TRACE fprintf(stderr, "guard 934 %ld => %s\n", _x, _status != no_parse ? "yes" : "no");
        }
        case 471:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 471 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        if (_status == no_parse) {
          goto contin;
        }
        /* bind: ws */
        PACC_TRACE fprintf(stderr, "bind 473 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind ws @ rule 843, col %ld\n", _x);
        _pacc_save_core(843, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 472;
        _st = 843;
        /* call Words */
        goto top;
        case 472: /* return from Words */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 621);
        /* end bind: ws */
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "lit 474 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "lit 474 @ col %ld => ", _x);
        if (_x+1 <= _pacc->input_length && memcmp(")", _pacc->string + _x, 1) == 0) {
          _status = parsed;
          _x += 1;
        }
        else {
          _pacc_error(_pacc, ".\")\"", _x);
          _status = no_parse;
        }
        PACC_TRACE fprintf(stderr, "lit 474 %ld => %s\n", _x, _status != no_parse ? "yes" : "no");
        if (_status == no_parse) {
          goto contin;
        }
        _pacc_save_core(906, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 475;
        _st = 906;
        /* call optNl */
        goto top;
        case 475: /* return from optNl */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 621);
        if (_status == no_parse) {
          goto contin;
        }
        /* bind: c */
        PACC_TRACE fprintf(stderr, "bind 477 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind c @ rule 621, col %ld\n", _x);
        _pacc_save_core(621, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 476;
        _st = 621;
        /* call cmd */
        goto top;
        case 476: /* return from cmd */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 621);
        /* end bind: c */
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "expr 484 @ col %ld?\n", _x);
        assert(cur->expr_id == 0);
        cur->expr_id = 484;
        case 484:
        if (_evaling) {
          struct pacc_mid *_pacc_p;
          /* i is 0, type is struct Node * */
          struct Node * w;
          /* i is 1, type is struct Node * */
          struct Node * ws;
          /* i is 3, type is struct Node * */
          struct Node * c;
          PACC_TRACE fprintf(stderr, "484: evaluating\n");
          _pacc_p = cur = _pacc_result(_pacc, _x, 621);
          _pos = 0;
          PACC_TRACE fprintf(stderr, "binding of w: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind w to r695 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 695);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 480;
            _pacc_ev_i = 0; goto eval_loop;
            case 480:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          w = cur->value.u3;
          PACC_TRACE fprintf(stderr, "bound w to r695 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          _pos = 1;
          PACC_TRACE fprintf(stderr, "binding of ws: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind ws to r843 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 843);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 479;
            _pacc_ev_i = 0; goto eval_loop;
            case 479:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          ws = cur->value.u3;
          PACC_TRACE fprintf(stderr, "bound ws to r843 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          _pos = 3;
          PACC_TRACE fprintf(stderr, "binding of c: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind c to r621 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 621);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 478;
            _pacc_ev_i = 0; goto eval_loop;
            case 478:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          c = cur->value.u3;
          PACC_TRACE fprintf(stderr, "bound c to r621 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          cur = _pacc_p;
          cur->value.u3=
#line 124 "parse.pacc"
  ( mk(nForin, w, ws, c) )
#line 4131 "parse.c"
          ;
          PACC_TRACE fprintf(stderr, "stash " TYPE_PRINTF " to (%ld, 621)\n", cur->value.u0, _x);
          goto _pacc_expr_done;
        }
        case 485:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 485 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 619 @ col %ld => %s\n", _x, _status!=no_parse?"yes":"no");
        if (_status != no_parse) {
          PACC_TRACE fprintf(stderr, "accept column registers\n");
          _pacc_Discard(cur->ev_valid); _pacc_Discard(_x);
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "restore column registers\n");
        _pacc_Pop(cur->ev_valid); _pacc_Pop(_x);
        PACC_TRACE fprintf(stderr, "save column registers\n");
        _pacc_Push(_x); _pacc_Push(cur->ev_valid);
        PACC_TRACE fprintf(stderr, "col restored to %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 619 @ col %ld? (next alternative)\n", _x);
        PACC_TRACE fprintf(stderr, "seq 502 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 502;
        _status = parsed;
        PACC_TRACE fprintf(stderr, "seq 487 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 487;
        _status = parsed;
        /* bind: _pacc_bl487 */
        PACC_TRACE fprintf(stderr, "bind 938 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind _pacc_bl487 @ rule 885, col %ld\n", _x);
        _pacc_save_core(885, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 486;
        _st = 885;
        /* call Word */
        goto top;
        case 486: /* return from Word */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 621);
        /* end bind: _pacc_bl487 */
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "guard 937 @ col %ld?\n", _x);
        /* 937: guard_pre() */
           {
          struct pacc_mid *_pacc_p;
          /* i is 0, type is ref_t */
          ref_t _pacc_bl487;
          _pacc_p = cur; _evaling = 1;
          _pos = 0;
          PACC_TRACE fprintf(stderr, "binding of _pacc_bl487: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind _pacc_bl487 to r885 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 885);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 936;
            _pacc_ev_i = 0; goto eval_loop;
            case 936:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          _pacc_bl487 = cur->value.u4;
          PACC_TRACE fprintf(stderr, "bound _pacc_bl487 to r885 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          cur = _pacc_p; _evaling = 0;
          _status = (
(ref_streq(_pacc_bl487,"for"))
#line 4203 "parse.c"
          ) ? parsed : no_parse;
          PACC_TRACE fprintf(stderr, "guard 937 %ld => %s\n", _x, _status != no_parse ? "yes" : "no");
        }
        case 487:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 487 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "lit 488 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "lit 488 @ col %ld => ", _x);
        if (_x+1 <= _pacc->input_length && memcmp("(", _pacc->string + _x, 1) == 0) {
          _status = parsed;
          _x += 1;
        }
        else {
          _pacc_error(_pacc, ".\"(\"", _x);
          _status = no_parse;
        }
        PACC_TRACE fprintf(stderr, "lit 488 %ld => %s\n", _x, _status != no_parse ? "yes" : "no");
        if (_status == no_parse) {
          goto contin;
        }
        /* bind: w */
        PACC_TRACE fprintf(stderr, "bind 490 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind w @ rule 695, col %ld\n", _x);
        _pacc_save_core(695, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 489;
        _st = 695;
        /* call word */
        goto top;
        case 489: /* return from word */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 621);
        /* end bind: w */
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "lit 491 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "lit 491 @ col %ld => ", _x);
        if (_x+1 <= _pacc->input_length && memcmp(")", _pacc->string + _x, 1) == 0) {
          _status = parsed;
          _x += 1;
        }
        else {
          _pacc_error(_pacc, ".\")\"", _x);
          _status = no_parse;
        }
        PACC_TRACE fprintf(stderr, "lit 491 %ld => %s\n", _x, _status != no_parse ? "yes" : "no");
        if (_status == no_parse) {
          goto contin;
        }
        _pacc_save_core(906, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 492;
        _st = 906;
        /* call optNl */
        goto top;
        case 492: /* return from optNl */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 621);
        if (_status == no_parse) {
          goto contin;
        }
        /* bind: c */
        PACC_TRACE fprintf(stderr, "bind 494 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind c @ rule 621, col %ld\n", _x);
        _pacc_save_core(621, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 493;
        _st = 621;
        /* call cmd */
        goto top;
        case 493: /* return from cmd */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 621);
        /* end bind: c */
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "expr 501 @ col %ld?\n", _x);
        assert(cur->expr_id == 0);
        cur->expr_id = 501;
        case 501:
        if (_evaling) {
          struct pacc_mid *_pacc_p;
          /* i is 0, type is struct Node * */
          struct Node * w;
          /* i is 2, type is struct Node * */
          struct Node * c;
          PACC_TRACE fprintf(stderr, "501: evaluating\n");
          _pacc_p = cur = _pacc_result(_pacc, _x, 621);
          _pos = 0;
          PACC_TRACE fprintf(stderr, "binding of w: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind w to r695 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 695);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 497;
            _pacc_ev_i = 0; goto eval_loop;
            case 497:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          w = cur->value.u3;
          PACC_TRACE fprintf(stderr, "bound w to r695 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          _pos = 2;
          PACC_TRACE fprintf(stderr, "binding of c: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind c to r621 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 621);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 495;
            _pacc_ev_i = 0; goto eval_loop;
            case 495:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          c = cur->value.u3;
          PACC_TRACE fprintf(stderr, "bound c to r621 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          cur = _pacc_p;
          cur->value.u3=
#line 125 "parse.pacc"
                                         ( mk(nForin, w, star, c) )
#line 4340 "parse.c"
          ;
          PACC_TRACE fprintf(stderr, "stash " TYPE_PRINTF " to (%ld, 621)\n", cur->value.u0, _x);
          goto _pacc_expr_done;
        }
        case 502:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 502 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 619 @ col %ld => %s\n", _x, _status!=no_parse?"yes":"no");
        if (_status != no_parse) {
          PACC_TRACE fprintf(stderr, "accept column registers\n");
          _pacc_Discard(cur->ev_valid); _pacc_Discard(_x);
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "restore column registers\n");
        _pacc_Pop(cur->ev_valid); _pacc_Pop(_x);
        PACC_TRACE fprintf(stderr, "save column registers\n");
        _pacc_Push(_x); _pacc_Push(cur->ev_valid);
        PACC_TRACE fprintf(stderr, "col restored to %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 619 @ col %ld? (next alternative)\n", _x);
        PACC_TRACE fprintf(stderr, "seq 516 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 516;
        _status = parsed;
        PACC_TRACE fprintf(stderr, "seq 504 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 504;
        _status = parsed;
        /* bind: _pacc_bl504 */
        PACC_TRACE fprintf(stderr, "bind 941 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind _pacc_bl504 @ rule 885, col %ld\n", _x);
        _pacc_save_core(885, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 503;
        _st = 885;
        /* call Word */
        goto top;
        case 503: /* return from Word */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 621);
        /* end bind: _pacc_bl504 */
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "guard 940 @ col %ld?\n", _x);
        /* 940: guard_pre() */
           {
          struct pacc_mid *_pacc_p;
          /* i is 0, type is ref_t */
          ref_t _pacc_bl504;
          _pacc_p = cur; _evaling = 1;
          _pos = 0;
          PACC_TRACE fprintf(stderr, "binding of _pacc_bl504: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind _pacc_bl504 to r885 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 885);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 939;
            _pacc_ev_i = 0; goto eval_loop;
            case 939:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          _pacc_bl504 = cur->value.u4;
          PACC_TRACE fprintf(stderr, "bound _pacc_bl504 to r885 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          cur = _pacc_p; _evaling = 0;
          _status = (
(ref_streq(_pacc_bl504,"while"))
#line 4412 "parse.c"
          ) ? parsed : no_parse;
          PACC_TRACE fprintf(stderr, "guard 940 %ld => %s\n", _x, _status != no_parse ? "yes" : "no");
        }
        case 504:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 504 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        if (_status == no_parse) {
          goto contin;
        }
        /* bind: p */
        PACC_TRACE fprintf(stderr, "bind 506 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind p @ rule 231, col %ld\n", _x);
        _pacc_save_core(231, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 505;
        _st = 231;
        /* call paren */
        goto top;
        case 505: /* return from paren */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 621);
        /* end bind: p */
        if (_status == no_parse) {
          goto contin;
        }
        _pacc_save_core(906, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 507;
        _st = 906;
        /* call optNl */
        goto top;
        case 507: /* return from optNl */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 621);
        if (_status == no_parse) {
          goto contin;
        }
        /* bind: c */
        PACC_TRACE fprintf(stderr, "bind 509 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind c @ rule 621, col %ld\n", _x);
        _pacc_save_core(621, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 508;
        _st = 621;
        /* call cmd */
        goto top;
        case 508: /* return from cmd */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 621);
        /* end bind: c */
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "expr 515 @ col %ld?\n", _x);
        assert(cur->expr_id == 0);
        cur->expr_id = 515;
        case 515:
        if (_evaling) {
          struct pacc_mid *_pacc_p;
          /* i is 0, type is Node * */
          Node * p;
          /* i is 2, type is struct Node * */
          struct Node * c;
          PACC_TRACE fprintf(stderr, "515: evaluating\n");
          _pacc_p = cur = _pacc_result(_pacc, _x, 621);
          _pos = 0;
          PACC_TRACE fprintf(stderr, "binding of p: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind p to r231 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 231);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 511;
            _pacc_ev_i = 0; goto eval_loop;
            case 511:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          p = cur->value.u0;
          PACC_TRACE fprintf(stderr, "bound p to r231 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          _pos = 2;
          PACC_TRACE fprintf(stderr, "binding of c: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind c to r621 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 621);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 510;
            _pacc_ev_i = 0; goto eval_loop;
            case 510:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          c = cur->value.u3;
          PACC_TRACE fprintf(stderr, "bound c to r621 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          cur = _pacc_p;
          cur->value.u3=
#line 126 "parse.pacc"
                                    ( mk(nWhile, p, c) )
#line 4521 "parse.c"
          ;
          PACC_TRACE fprintf(stderr, "stash " TYPE_PRINTF " to (%ld, 621)\n", cur->value.u0, _x);
          goto _pacc_expr_done;
        }
        case 516:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 516 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 619 @ col %ld => %s\n", _x, _status!=no_parse?"yes":"no");
        if (_status != no_parse) {
          PACC_TRACE fprintf(stderr, "accept column registers\n");
          _pacc_Discard(cur->ev_valid); _pacc_Discard(_x);
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "restore column registers\n");
        _pacc_Pop(cur->ev_valid); _pacc_Pop(_x);
        PACC_TRACE fprintf(stderr, "save column registers\n");
        _pacc_Push(_x); _pacc_Push(cur->ev_valid);
        PACC_TRACE fprintf(stderr, "col restored to %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 619 @ col %ld? (next alternative)\n", _x);
        PACC_TRACE fprintf(stderr, "seq 534 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 534;
        _status = parsed;
        PACC_TRACE fprintf(stderr, "seq 518 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 518;
        _status = parsed;
        /* bind: _pacc_bl518 */
        PACC_TRACE fprintf(stderr, "bind 944 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind _pacc_bl518 @ rule 885, col %ld\n", _x);
        _pacc_save_core(885, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 517;
        _st = 885;
        /* call Word */
        goto top;
        case 517: /* return from Word */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 621);
        /* end bind: _pacc_bl518 */
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "guard 943 @ col %ld?\n", _x);
        /* 943: guard_pre() */
           {
          struct pacc_mid *_pacc_p;
          /* i is 0, type is ref_t */
          ref_t _pacc_bl518;
          _pacc_p = cur; _evaling = 1;
          _pos = 0;
          PACC_TRACE fprintf(stderr, "binding of _pacc_bl518: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind _pacc_bl518 to r885 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 885);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 942;
            _pacc_ev_i = 0; goto eval_loop;
            case 942:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          _pacc_bl518 = cur->value.u4;
          PACC_TRACE fprintf(stderr, "bound _pacc_bl518 to r885 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          cur = _pacc_p; _evaling = 0;
          _status = (
(ref_streq(_pacc_bl518,"switch"))
#line 4593 "parse.c"
          ) ? parsed : no_parse;
          PACC_TRACE fprintf(stderr, "guard 943 %ld => %s\n", _x, _status != no_parse ? "yes" : "no");
        }
        case 518:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 518 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "lit 519 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "lit 519 @ col %ld => ", _x);
        if (_x+1 <= _pacc->input_length && memcmp("(", _pacc->string + _x, 1) == 0) {
          _status = parsed;
          _x += 1;
        }
        else {
          _pacc_error(_pacc, ".\"(\"", _x);
          _status = no_parse;
        }
        PACC_TRACE fprintf(stderr, "lit 519 %ld => %s\n", _x, _status != no_parse ? "yes" : "no");
        if (_status == no_parse) {
          goto contin;
        }
        /* bind: w */
        PACC_TRACE fprintf(stderr, "bind 521 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind w @ rule 695, col %ld\n", _x);
        _pacc_save_core(695, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 520;
        _st = 695;
        /* call word */
        goto top;
        case 520: /* return from word */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 621);
        /* end bind: w */
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "lit 522 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "lit 522 @ col %ld => ", _x);
        if (_x+1 <= _pacc->input_length && memcmp(")", _pacc->string + _x, 1) == 0) {
          _status = parsed;
          _x += 1;
        }
        else {
          _pacc_error(_pacc, ".\")\"", _x);
          _status = no_parse;
        }
        PACC_TRACE fprintf(stderr, "lit 522 %ld => %s\n", _x, _status != no_parse ? "yes" : "no");
        if (_status == no_parse) {
          goto contin;
        }
        _pacc_save_core(906, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 523;
        _st = 906;
        /* call optNl */
        goto top;
        case 523: /* return from optNl */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 621);
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "lit 524 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "lit 524 @ col %ld => ", _x);
        if (_x+1 <= _pacc->input_length && memcmp("{", _pacc->string + _x, 1) == 0) {
          _status = parsed;
          _x += 1;
        }
        else {
          _pacc_error(_pacc, ".\"{\"", _x);
          _status = no_parse;
        }
        PACC_TRACE fprintf(stderr, "lit 524 %ld => %s\n", _x, _status != no_parse ? "yes" : "no");
        if (_status == no_parse) {
          goto contin;
        }
        /* bind: c */
        PACC_TRACE fprintf(stderr, "bind 526 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind c @ rule 407, col %ld\n", _x);
        _pacc_save_core(407, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 525;
        _st = 407;
        /* call cbody */
        goto top;
        case 525: /* return from cbody */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 621);
        /* end bind: c */
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "lit 527 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "lit 527 @ col %ld => ", _x);
        if (_x+1 <= _pacc->input_length && memcmp("}", _pacc->string + _x, 1) == 0) {
          _status = parsed;
          _x += 1;
        }
        else {
          _pacc_error(_pacc, ".\"}\"", _x);
          _status = no_parse;
        }
        PACC_TRACE fprintf(stderr, "lit 527 %ld => %s\n", _x, _status != no_parse ? "yes" : "no");
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "expr 533 @ col %ld?\n", _x);
        assert(cur->expr_id == 0);
        cur->expr_id = 533;
        case 533:
        if (_evaling) {
          struct pacc_mid *_pacc_p;
          /* i is 0, type is struct Node * */
          struct Node * w;
          /* i is 2, type is struct Node * */
          struct Node * c;
          PACC_TRACE fprintf(stderr, "533: evaluating\n");
          _pacc_p = cur = _pacc_result(_pacc, _x, 621);
          _pos = 0;
          PACC_TRACE fprintf(stderr, "binding of w: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind w to r695 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 695);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 529;
            _pacc_ev_i = 0; goto eval_loop;
            case 529:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          w = cur->value.u3;
          PACC_TRACE fprintf(stderr, "bound w to r695 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          _pos = 2;
          PACC_TRACE fprintf(stderr, "binding of c: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind c to r407 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 407);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 528;
            _pacc_ev_i = 0; goto eval_loop;
            case 528:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          c = cur->value.u3;
          PACC_TRACE fprintf(stderr, "bound c to r407 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          cur = _pacc_p;
          cur->value.u3=
#line 127 "parse.pacc"
                                                      ( mk(nSwitch, w, c) )
#line 4758 "parse.c"
          ;
          PACC_TRACE fprintf(stderr, "stash " TYPE_PRINTF " to (%ld, 621)\n", cur->value.u0, _x);
          goto _pacc_expr_done;
        }
        case 534:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 534 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 619 @ col %ld => %s\n", _x, _status!=no_parse?"yes":"no");
        if (_status != no_parse) {
          PACC_TRACE fprintf(stderr, "accept column registers\n");
          _pacc_Discard(cur->ev_valid); _pacc_Discard(_x);
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "restore column registers\n");
        _pacc_Pop(cur->ev_valid); _pacc_Pop(_x);
        PACC_TRACE fprintf(stderr, "save column registers\n");
        _pacc_Push(_x); _pacc_Push(cur->ev_valid);
        PACC_TRACE fprintf(stderr, "col restored to %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 619 @ col %ld? (next alternative)\n", _x);
        PACC_TRACE fprintf(stderr, "seq 547 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 547;
        _status = parsed;
        _pacc_save_core(916, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 535;
        _st = 916;
        /* call Tilde */
        goto top;
        case 535: /* return from Tilde */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 621);
        if (_status == no_parse) {
          goto contin;
        }
        _pacc_save_core(901, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 536;
        _st = 901;
        /* call optCaret */
        goto top;
        case 536: /* return from optCaret */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 621);
        if (_status == no_parse) {
          goto contin;
        }
        /* bind: w */
        PACC_TRACE fprintf(stderr, "bind 538 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind w @ rule 695, col %ld\n", _x);
        _pacc_save_core(695, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 537;
        _st = 695;
        /* call word */
        goto top;
        case 537: /* return from word */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 621);
        /* end bind: w */
        if (_status == no_parse) {
          goto contin;
        }
        /* bind: ws */
        PACC_TRACE fprintf(stderr, "bind 540 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind ws @ rule 843, col %ld\n", _x);
        _pacc_save_core(843, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 539;
        _st = 843;
        /* call Words */
        goto top;
        case 539: /* return from Words */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 621);
        /* end bind: ws */
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "expr 546 @ col %ld?\n", _x);
        assert(cur->expr_id == 0);
        cur->expr_id = 546;
        case 546:
        if (_evaling) {
          struct pacc_mid *_pacc_p;
          /* i is 2, type is struct Node * */
          struct Node * w;
          /* i is 3, type is struct Node * */
          struct Node * ws;
          PACC_TRACE fprintf(stderr, "546: evaluating\n");
          _pacc_p = cur = _pacc_result(_pacc, _x, 621);
          _pos = 2;
          PACC_TRACE fprintf(stderr, "binding of w: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind w to r695 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 695);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 542;
            _pacc_ev_i = 0; goto eval_loop;
            case 542:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          w = cur->value.u3;
          PACC_TRACE fprintf(stderr, "bound w to r695 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          _pos = 3;
          PACC_TRACE fprintf(stderr, "binding of ws: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind ws to r843 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 843);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 541;
            _pacc_ev_i = 0; goto eval_loop;
            case 541:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          ws = cur->value.u3;
          PACC_TRACE fprintf(stderr, "bound ws to r843 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          cur = _pacc_p;
          cur->value.u3=
#line 128 "parse.pacc"
                                  ( mk(nMatch, w, ws) )
#line 4897 "parse.c"
          ;
          PACC_TRACE fprintf(stderr, "stash " TYPE_PRINTF " to (%ld, 621)\n", cur->value.u0, _x);
          goto _pacc_expr_done;
        }
        case 547:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 547 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 619 @ col %ld => %s\n", _x, _status!=no_parse?"yes":"no");
        if (_status != no_parse) {
          PACC_TRACE fprintf(stderr, "accept column registers\n");
          _pacc_Discard(cur->ev_valid); _pacc_Discard(_x);
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "restore column registers\n");
        _pacc_Pop(cur->ev_valid); _pacc_Pop(_x);
        PACC_TRACE fprintf(stderr, "save column registers\n");
        _pacc_Push(_x); _pacc_Push(cur->ev_valid);
        PACC_TRACE fprintf(stderr, "col restored to %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 619 @ col %ld? (next alternative)\n", _x);
        PACC_TRACE fprintf(stderr, "seq 561 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 561;
        _status = parsed;
        /* bind: r */
        PACC_TRACE fprintf(stderr, "bind 549 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind r @ rule 298, col %ld\n", _x);
        _pacc_save_core(298, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 548;
        _st = 298;
        /* call redir */
        goto top;
        case 548: /* return from redir */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 621);
        /* end bind: r */
        if (_status == no_parse) {
          goto contin;
        }
        /* bind: c */
        PACC_TRACE fprintf(stderr, "bind 551 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind c @ rule 621, col %ld\n", _x);
        _pacc_save_core(621, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 550;
        _st = 621;
        /* call cmd */
        goto top;
        case 550: /* return from cmd */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 621);
        /* end bind: c */
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "expr 560 @ col %ld?\n", _x);
        assert(cur->expr_id == 0);
        cur->expr_id = 560;
        case 560:
        if (_evaling) {
          struct pacc_mid *_pacc_p;
          /* i is 1, type is struct Node * */
          struct Node * c;
          /* i is 0, type is Node * */
          Node * r;
          PACC_TRACE fprintf(stderr, "560: evaluating\n");
          _pacc_p = cur = _pacc_result(_pacc, _x, 621);
          _pos = 1;
          PACC_TRACE fprintf(stderr, "binding of c: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind c to r621 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 621);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 553;
            _pacc_ev_i = 0; goto eval_loop;
            case 553:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          c = cur->value.u3;
          PACC_TRACE fprintf(stderr, "bound c to r621 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          _pos = 0;
          PACC_TRACE fprintf(stderr, "binding of r: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind r to r298 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 298);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 552;
            _pacc_ev_i = 0; goto eval_loop;
            case 552:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          r = cur->value.u0;
          PACC_TRACE fprintf(stderr, "bound r to r298 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          cur = _pacc_p;
          cur->value.u3=
#line 132 "parse.pacc"
                   ( (c != NULL ? mk(nPre, r, c) : r) )
#line 5004 "parse.c"
          ;
          PACC_TRACE fprintf(stderr, "stash " TYPE_PRINTF " to (%ld, 621)\n", cur->value.u0, _x);
          goto _pacc_expr_done;
        }
        case 561:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 561 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 619 @ col %ld => %s\n", _x, _status!=no_parse?"yes":"no");
        if (_status != no_parse) {
          PACC_TRACE fprintf(stderr, "accept column registers\n");
          _pacc_Discard(cur->ev_valid); _pacc_Discard(_x);
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "restore column registers\n");
        _pacc_Pop(cur->ev_valid); _pacc_Pop(_x);
        PACC_TRACE fprintf(stderr, "save column registers\n");
        _pacc_Push(_x); _pacc_Push(cur->ev_valid);
        PACC_TRACE fprintf(stderr, "col restored to %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 619 @ col %ld? (next alternative)\n", _x);
        PACC_TRACE fprintf(stderr, "seq 575 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 575;
        _status = parsed;
        /* bind: a */
        PACC_TRACE fprintf(stderr, "bind 563 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind a @ rule 245, col %ld\n", _x);
        _pacc_save_core(245, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 562;
        _st = 245;
        /* call assign */
        goto top;
        case 562: /* return from assign */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 621);
        /* end bind: a */
        if (_status == no_parse) {
          goto contin;
        }
        /* bind: c */
        PACC_TRACE fprintf(stderr, "bind 565 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind c @ rule 621, col %ld\n", _x);
        _pacc_save_core(621, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 564;
        _st = 621;
        /* call cmd */
        goto top;
        case 564: /* return from cmd */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 621);
        /* end bind: c */
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "expr 574 @ col %ld?\n", _x);
        assert(cur->expr_id == 0);
        cur->expr_id = 574;
        case 574:
        if (_evaling) {
          struct pacc_mid *_pacc_p;
          /* i is 1, type is struct Node * */
          struct Node * c;
          /* i is 0, type is Node * */
          Node * a;
          PACC_TRACE fprintf(stderr, "574: evaluating\n");
          _pacc_p = cur = _pacc_result(_pacc, _x, 621);
          _pos = 1;
          PACC_TRACE fprintf(stderr, "binding of c: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind c to r621 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 621);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 567;
            _pacc_ev_i = 0; goto eval_loop;
            case 567:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          c = cur->value.u3;
          PACC_TRACE fprintf(stderr, "bound c to r621 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          _pos = 0;
          PACC_TRACE fprintf(stderr, "binding of a: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind a to r245 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 245);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 566;
            _pacc_ev_i = 0; goto eval_loop;
            case 566:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          a = cur->value.u0;
          PACC_TRACE fprintf(stderr, "bound a to r245 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          cur = _pacc_p;
          cur->value.u3=
#line 133 "parse.pacc"
                   ( (c != NULL ? mk(nPre, a, c) : a) )
#line 5111 "parse.c"
          ;
          PACC_TRACE fprintf(stderr, "stash " TYPE_PRINTF " to (%ld, 621)\n", cur->value.u0, _x);
          goto _pacc_expr_done;
        }
        case 575:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 575 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 619 @ col %ld => %s\n", _x, _status!=no_parse?"yes":"no");
        if (_status != no_parse) {
          PACC_TRACE fprintf(stderr, "accept column registers\n");
          _pacc_Discard(cur->ev_valid); _pacc_Discard(_x);
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "restore column registers\n");
        _pacc_Pop(cur->ev_valid); _pacc_Pop(_x);
        PACC_TRACE fprintf(stderr, "save column registers\n");
        _pacc_Push(_x); _pacc_Push(cur->ev_valid);
        PACC_TRACE fprintf(stderr, "col restored to %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 619 @ col %ld? (next alternative)\n", _x);
        PACC_TRACE fprintf(stderr, "seq 585 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 585;
        _status = parsed;
        _pacc_save_core(895, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 576;
        _st = 895;
        /* call Bang */
        goto top;
        case 576: /* return from Bang */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 621);
        if (_status == no_parse) {
          goto contin;
        }
        _pacc_save_core(901, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 577;
        _st = 901;
        /* call optCaret */
        goto top;
        case 577: /* return from optCaret */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 621);
        if (_status == no_parse) {
          goto contin;
        }
        /* bind: c */
        PACC_TRACE fprintf(stderr, "bind 579 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind c @ rule 621, col %ld\n", _x);
        _pacc_save_core(621, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 578;
        _st = 621;
        /* call cmd */
        goto top;
        case 578: /* return from cmd */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 621);
        /* end bind: c */
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "expr 584 @ col %ld?\n", _x);
        assert(cur->expr_id == 0);
        cur->expr_id = 584;
        case 584:
        if (_evaling) {
          struct pacc_mid *_pacc_p;
          /* i is 2, type is struct Node * */
          struct Node * c;
          PACC_TRACE fprintf(stderr, "584: evaluating\n");
          _pacc_p = cur = _pacc_result(_pacc, _x, 621);
          _pos = 2;
          PACC_TRACE fprintf(stderr, "binding of c: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind c to r621 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 621);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 580;
            _pacc_ev_i = 0; goto eval_loop;
            case 580:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          c = cur->value.u3;
          PACC_TRACE fprintf(stderr, "bound c to r621 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          cur = _pacc_p;
          cur->value.u3=
#line 134 "parse.pacc"
                         ( mk(nBang, c) )
#line 5215 "parse.c"
          ;
          PACC_TRACE fprintf(stderr, "stash " TYPE_PRINTF " to (%ld, 621)\n", cur->value.u0, _x);
          goto _pacc_expr_done;
        }
        case 585:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 585 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 619 @ col %ld => %s\n", _x, _status!=no_parse?"yes":"no");
        if (_status != no_parse) {
          PACC_TRACE fprintf(stderr, "accept column registers\n");
          _pacc_Discard(cur->ev_valid); _pacc_Discard(_x);
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "restore column registers\n");
        _pacc_Pop(cur->ev_valid); _pacc_Pop(_x);
        PACC_TRACE fprintf(stderr, "save column registers\n");
        _pacc_Push(_x); _pacc_Push(cur->ev_valid);
        PACC_TRACE fprintf(stderr, "col restored to %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 619 @ col %ld? (next alternative)\n", _x);
        PACC_TRACE fprintf(stderr, "seq 595 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 595;
        _status = parsed;
        _pacc_save_core(890, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 586;
        _st = 890;
        /* call And */
        goto top;
        case 586: /* return from And */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 621);
        if (_status == no_parse) {
          goto contin;
        }
        _pacc_save_core(901, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 587;
        _st = 901;
        /* call optCaret */
        goto top;
        case 587: /* return from optCaret */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 621);
        if (_status == no_parse) {
          goto contin;
        }
        /* bind: c */
        PACC_TRACE fprintf(stderr, "bind 589 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind c @ rule 621, col %ld\n", _x);
        _pacc_save_core(621, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 588;
        _st = 621;
        /* call cmd */
        goto top;
        case 588: /* return from cmd */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 621);
        /* end bind: c */
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "expr 594 @ col %ld?\n", _x);
        assert(cur->expr_id == 0);
        cur->expr_id = 594;
        case 594:
        if (_evaling) {
          struct pacc_mid *_pacc_p;
          /* i is 2, type is struct Node * */
          struct Node * c;
          PACC_TRACE fprintf(stderr, "594: evaluating\n");
          _pacc_p = cur = _pacc_result(_pacc, _x, 621);
          _pos = 2;
          PACC_TRACE fprintf(stderr, "binding of c: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind c to r621 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 621);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 590;
            _pacc_ev_i = 0; goto eval_loop;
            case 590:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          c = cur->value.u3;
          PACC_TRACE fprintf(stderr, "bound c to r621 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          cur = _pacc_p;
          cur->value.u3=
#line 135 "parse.pacc"
                        ( mk(nSubshell, c) )
#line 5319 "parse.c"
          ;
          PACC_TRACE fprintf(stderr, "stash " TYPE_PRINTF " to (%ld, 621)\n", cur->value.u0, _x);
          goto _pacc_expr_done;
        }
        case 595:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 595 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 619 @ col %ld => %s\n", _x, _status!=no_parse?"yes":"no");
        if (_status != no_parse) {
          PACC_TRACE fprintf(stderr, "accept column registers\n");
          _pacc_Discard(cur->ev_valid); _pacc_Discard(_x);
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "restore column registers\n");
        _pacc_Pop(cur->ev_valid); _pacc_Pop(_x);
        PACC_TRACE fprintf(stderr, "save column registers\n");
        _pacc_Push(_x); _pacc_Push(cur->ev_valid);
        PACC_TRACE fprintf(stderr, "col restored to %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 619 @ col %ld? (next alternative)\n", _x);
        PACC_TRACE fprintf(stderr, "seq 608 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 608;
        _status = parsed;
        PACC_TRACE fprintf(stderr, "seq 597 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 597;
        _status = parsed;
        /* bind: _pacc_bl597 */
        PACC_TRACE fprintf(stderr, "bind 947 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind _pacc_bl597 @ rule 885, col %ld\n", _x);
        _pacc_save_core(885, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 596;
        _st = 885;
        /* call Word */
        goto top;
        case 596: /* return from Word */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 621);
        /* end bind: _pacc_bl597 */
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "guard 946 @ col %ld?\n", _x);
        /* 946: guard_pre() */
           {
          struct pacc_mid *_pacc_p;
          /* i is 0, type is ref_t */
          ref_t _pacc_bl597;
          _pacc_p = cur; _evaling = 1;
          _pos = 0;
          PACC_TRACE fprintf(stderr, "binding of _pacc_bl597: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind _pacc_bl597 to r885 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 885);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 945;
            _pacc_ev_i = 0; goto eval_loop;
            case 945:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          _pacc_bl597 = cur->value.u4;
          PACC_TRACE fprintf(stderr, "bound _pacc_bl597 to r885 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          cur = _pacc_p; _evaling = 0;
          _status = (
(ref_streq(_pacc_bl597,"fn"))
#line 5391 "parse.c"
          ) ? parsed : no_parse;
          PACC_TRACE fprintf(stderr, "guard 946 %ld => %s\n", _x, _status != no_parse ? "yes" : "no");
        }
        case 597:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 597 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        if (_status == no_parse) {
          goto contin;
        }
        /* bind: ws */
        PACC_TRACE fprintf(stderr, "bind 599 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind ws @ rule 843, col %ld\n", _x);
        _pacc_save_core(843, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 598;
        _st = 843;
        /* call Words */
        goto top;
        case 598: /* return from Words */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 621);
        /* end bind: ws */
        if (_status == no_parse) {
          goto contin;
        }
        /* bind: b */
        PACC_TRACE fprintf(stderr, "bind 601 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind b @ rule 221, col %ld\n", _x);
        _pacc_save_core(221, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 600;
        _st = 221;
        /* call brace */
        goto top;
        case 600: /* return from brace */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 621);
        /* end bind: b */
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "expr 607 @ col %ld?\n", _x);
        assert(cur->expr_id == 0);
        cur->expr_id = 607;
        case 607:
        if (_evaling) {
          struct pacc_mid *_pacc_p;
          /* i is 0, type is struct Node * */
          struct Node * ws;
          /* i is 1, type is Node * */
          Node * b;
          PACC_TRACE fprintf(stderr, "607: evaluating\n");
          _pacc_p = cur = _pacc_result(_pacc, _x, 621);
          _pos = 0;
          PACC_TRACE fprintf(stderr, "binding of ws: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind ws to r843 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 843);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 603;
            _pacc_ev_i = 0; goto eval_loop;
            case 603:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          ws = cur->value.u3;
          PACC_TRACE fprintf(stderr, "bound ws to r843 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          _pos = 1;
          PACC_TRACE fprintf(stderr, "binding of b: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind b to r221 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 221);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 602;
            _pacc_ev_i = 0; goto eval_loop;
            case 602:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          b = cur->value.u0;
          PACC_TRACE fprintf(stderr, "bound b to r221 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          cur = _pacc_p;
          cur->value.u3=
#line 136 "parse.pacc"
                               ( mk(nNewfn, ws, b) )
#line 5484 "parse.c"
          ;
          PACC_TRACE fprintf(stderr, "stash " TYPE_PRINTF " to (%ld, 621)\n", cur->value.u0, _x);
          goto _pacc_expr_done;
        }
        case 608:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 608 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 619 @ col %ld => %s\n", _x, _status!=no_parse?"yes":"no");
        if (_status != no_parse) {
          PACC_TRACE fprintf(stderr, "accept column registers\n");
          _pacc_Discard(cur->ev_valid); _pacc_Discard(_x);
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "restore column registers\n");
        _pacc_Pop(cur->ev_valid); _pacc_Pop(_x);
        PACC_TRACE fprintf(stderr, "save column registers\n");
        _pacc_Push(_x); _pacc_Push(cur->ev_valid);
        PACC_TRACE fprintf(stderr, "col restored to %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 619 @ col %ld? (next alternative)\n", _x);
        PACC_TRACE fprintf(stderr, "seq 618 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 618;
        _status = parsed;
        PACC_TRACE fprintf(stderr, "seq 610 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 610;
        _status = parsed;
        /* bind: _pacc_bl610 */
        PACC_TRACE fprintf(stderr, "bind 950 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind _pacc_bl610 @ rule 885, col %ld\n", _x);
        _pacc_save_core(885, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 609;
        _st = 885;
        /* call Word */
        goto top;
        case 609: /* return from Word */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 621);
        /* end bind: _pacc_bl610 */
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "guard 949 @ col %ld?\n", _x);
        /* 949: guard_pre() */
           {
          struct pacc_mid *_pacc_p;
          /* i is 0, type is ref_t */
          ref_t _pacc_bl610;
          _pacc_p = cur; _evaling = 1;
          _pos = 0;
          PACC_TRACE fprintf(stderr, "binding of _pacc_bl610: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind _pacc_bl610 to r885 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 885);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 948;
            _pacc_ev_i = 0; goto eval_loop;
            case 948:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          _pacc_bl610 = cur->value.u4;
          PACC_TRACE fprintf(stderr, "bound _pacc_bl610 to r885 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          cur = _pacc_p; _evaling = 0;
          _status = (
(ref_streq(_pacc_bl610,"fn"))
#line 5556 "parse.c"
          ) ? parsed : no_parse;
          PACC_TRACE fprintf(stderr, "guard 949 %ld => %s\n", _x, _status != no_parse ? "yes" : "no");
        }
        case 610:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 610 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        if (_status == no_parse) {
          goto contin;
        }
        /* bind: ws */
        PACC_TRACE fprintf(stderr, "bind 612 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind ws @ rule 843, col %ld\n", _x);
        _pacc_save_core(843, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 611;
        _st = 843;
        /* call Words */
        goto top;
        case 611: /* return from Words */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 621);
        /* end bind: ws */
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "expr 617 @ col %ld?\n", _x);
        assert(cur->expr_id == 0);
        cur->expr_id = 617;
        case 617:
        if (_evaling) {
          struct pacc_mid *_pacc_p;
          /* i is 0, type is struct Node * */
          struct Node * ws;
          PACC_TRACE fprintf(stderr, "617: evaluating\n");
          _pacc_p = cur = _pacc_result(_pacc, _x, 621);
          _pos = 0;
          PACC_TRACE fprintf(stderr, "binding of ws: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind ws to r843 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 843);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 613;
            _pacc_ev_i = 0; goto eval_loop;
            case 613:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          ws = cur->value.u3;
          PACC_TRACE fprintf(stderr, "bound ws to r843 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          cur = _pacc_p;
          cur->value.u3=
#line 137 "parse.pacc"
                        ( mk(nRmfn, ws) )
#line 5614 "parse.c"
          ;
          PACC_TRACE fprintf(stderr, "stash " TYPE_PRINTF " to (%ld, 621)\n", cur->value.u0, _x);
          goto _pacc_expr_done;
        }
        case 618:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 618 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        if (_status == no_parse) {
          PACC_TRACE fprintf(stderr, "restore column registers\n");
          _pacc_Pop(cur->ev_valid); _pacc_Pop(_x);
        }
        else {
          PACC_TRACE fprintf(stderr, "accept column registers\n");
          _pacc_Discard(cur->ev_valid); _pacc_Discard(_x);
        }
        case 619:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "alt 619 @ col %ld => %s\n", _x, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        cur->rule = (cur->rule & ~3) | _status;
        cur->remainder = _x;
        if (_pacc->err_col == _x_rule) {
          _pacc->err_valid = 0;
          _pacc_error(_pacc, ".cmd", _x_rule);
        }
      }
      goto contin;
      case 634: /* SimpleRedir */
      PACC_TRACE fprintf(stderr, "rule 634 (SimpleRedir) col %ld\n", _x);
      _x_rule = _x;
      cur = _pacc_result(_pacc, _x, 634);
      if ((cur->rule & 3) == uncomputed) {
        PACC_TRACE fprintf(stderr, "seq 632 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 632;
        _status = parsed;
        /* bind: s */
        PACC_TRACE fprintf(stderr, "bind 623 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind s @ rule 654, col %ld\n", _x);
        _pacc_save_core(654, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 622;
        _st = 654;
        /* call Simple */
        goto top;
        case 622: /* return from Simple */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 634);
        /* end bind: s */
        if (_status == no_parse) {
          goto contin;
        }
        /* bind: r */
        PACC_TRACE fprintf(stderr, "bind 625 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind r @ rule 326, col %ld\n", _x);
        _pacc_save_core(326, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 624;
        _st = 326;
        /* call Redir */
        goto top;
        case 624: /* return from Redir */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 634);
        /* end bind: r */
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "expr 631 @ col %ld?\n", _x);
        assert(cur->expr_id == 0);
        cur->expr_id = 631;
        case 631:
        if (_evaling) {
          struct pacc_mid *_pacc_p;
          /* i is 0, type is struct Node * */
          struct Node * s;
          /* i is 1, type is redirtype */
          redirtype r;
          PACC_TRACE fprintf(stderr, "631: evaluating\n");
          _pacc_p = cur = _pacc_result(_pacc, _x, 634);
          _pos = 0;
          PACC_TRACE fprintf(stderr, "binding of s: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind s to r654 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 654);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 627;
            _pacc_ev_i = 0; goto eval_loop;
            case 627:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          s = cur->value.u3;
          PACC_TRACE fprintf(stderr, "bound s to r654 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          _pos = 1;
          PACC_TRACE fprintf(stderr, "binding of r: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind r to r326 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 326);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 626;
            _pacc_ev_i = 0; goto eval_loop;
            case 626:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          r = cur->value.u1;
          PACC_TRACE fprintf(stderr, "bound r to r326 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          cur = _pacc_p;
          cur->value.u3=
#line 139 "parse.pacc"
                               ( mk(nArgs, s, r) )
#line 5734 "parse.c"
          ;
          PACC_TRACE fprintf(stderr, "stash " TYPE_PRINTF " to (%ld, 634)\n", cur->value.u0, _x);
          goto _pacc_expr_done;
        }
        case 632:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 632 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        cur->rule = (cur->rule & ~3) | _status;
        cur->remainder = _x;
        if (_pacc->err_col == _x_rule) {
          _pacc->err_valid = 0;
          _pacc_error(_pacc, ".SimpleRedir", _x_rule);
        }
      }
      goto contin;
      case 654: /* Simple */
      PACC_TRACE fprintf(stderr, "rule 654 (Simple) col %ld\n", _x);
      _x_rule = _x;
      cur = _pacc_result(_pacc, _x, 654);
      if ((cur->rule & 3) == uncomputed) {
        PACC_TRACE fprintf(stderr, "alt 652 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 652;
        PACC_TRACE fprintf(stderr, "save column registers\n");
        _pacc_Push(_x); _pacc_Push(cur->ev_valid);
        PACC_TRACE fprintf(stderr, "seq 640 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 640;
        _status = parsed;
        /* bind: a */
        PACC_TRACE fprintf(stderr, "bind 636 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind a @ rule 666, col %ld\n", _x);
        _pacc_save_core(666, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 635;
        _st = 666;
        /* call First */
        goto top;
        case 635: /* return from First */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 654);
        /* end bind: a */
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "expr 639 @ col %ld?\n", _x);
        assert(cur->expr_id == 0);
        cur->expr_id = 639;
        case 639:
        if (_evaling) {
          struct pacc_mid *_pacc_p;
          /* i is 0, type is struct Node * */
          struct Node * a;
          PACC_TRACE fprintf(stderr, "639: evaluating\n");
          _pacc_p = cur = _pacc_result(_pacc, _x, 654);
          _pos = 0;
          PACC_TRACE fprintf(stderr, "binding of a: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind a to r666 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 666);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 637;
            _pacc_ev_i = 0; goto eval_loop;
            case 637:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          a = cur->value.u3;
          PACC_TRACE fprintf(stderr, "bound a to r666 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          cur = _pacc_p;
          cur->value.u3=
#line 141 "parse.pacc"
                  (a)
#line 5812 "parse.c"
          ;
          PACC_TRACE fprintf(stderr, "stash " TYPE_PRINTF " to (%ld, 654)\n", cur->value.u0, _x);
          goto _pacc_expr_done;
        }
        case 640:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 640 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 652 @ col %ld => %s\n", _x, _status!=no_parse?"yes":"no");
        if (_status != no_parse) {
          PACC_TRACE fprintf(stderr, "accept column registers\n");
          _pacc_Discard(cur->ev_valid); _pacc_Discard(_x);
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "restore column registers\n");
        _pacc_Pop(cur->ev_valid); _pacc_Pop(_x);
        PACC_TRACE fprintf(stderr, "save column registers\n");
        _pacc_Push(_x); _pacc_Push(cur->ev_valid);
        PACC_TRACE fprintf(stderr, "col restored to %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 652 @ col %ld? (next alternative)\n", _x);
        PACC_TRACE fprintf(stderr, "seq 651 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 651;
        _status = parsed;
        /* bind: w */
        PACC_TRACE fprintf(stderr, "bind 642 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind w @ rule 666, col %ld\n", _x);
        _pacc_save_core(666, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 641;
        _st = 666;
        /* call First */
        goto top;
        case 641: /* return from First */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 654);
        /* end bind: w */
        if (_status == no_parse) {
          goto contin;
        }
        /* bind: ws */
        PACC_TRACE fprintf(stderr, "bind 644 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind ws @ rule 843, col %ld\n", _x);
        _pacc_save_core(843, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 643;
        _st = 843;
        /* call Words */
        goto top;
        case 643: /* return from Words */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 654);
        /* end bind: ws */
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "expr 650 @ col %ld?\n", _x);
        assert(cur->expr_id == 0);
        cur->expr_id = 650;
        case 650:
        if (_evaling) {
          struct pacc_mid *_pacc_p;
          /* i is 0, type is struct Node * */
          struct Node * w;
          /* i is 1, type is struct Node * */
          struct Node * ws;
          PACC_TRACE fprintf(stderr, "650: evaluating\n");
          _pacc_p = cur = _pacc_result(_pacc, _x, 654);
          _pos = 0;
          PACC_TRACE fprintf(stderr, "binding of w: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind w to r666 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 666);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 646;
            _pacc_ev_i = 0; goto eval_loop;
            case 646:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          w = cur->value.u3;
          PACC_TRACE fprintf(stderr, "bound w to r666 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          _pos = 1;
          PACC_TRACE fprintf(stderr, "binding of ws: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind ws to r843 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 843);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 645;
            _pacc_ev_i = 0; goto eval_loop;
            case 645:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          ws = cur->value.u3;
          PACC_TRACE fprintf(stderr, "bound ws to r843 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          cur = _pacc_p;
          cur->value.u3=
#line 142 "parse.pacc"
                    ( mk(nArgs, w, ws) )
#line 5919 "parse.c"
          ;
          PACC_TRACE fprintf(stderr, "stash " TYPE_PRINTF " to (%ld, 654)\n", cur->value.u0, _x);
          goto _pacc_expr_done;
        }
        case 651:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 651 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        if (_status == no_parse) {
          PACC_TRACE fprintf(stderr, "restore column registers\n");
          _pacc_Pop(cur->ev_valid); _pacc_Pop(_x);
        }
        else {
          PACC_TRACE fprintf(stderr, "accept column registers\n");
          _pacc_Discard(cur->ev_valid); _pacc_Discard(_x);
        }
        case 652:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "alt 652 @ col %ld => %s\n", _x, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        cur->rule = (cur->rule & ~3) | _status;
        cur->remainder = _x;
        if (_pacc->err_col == _x_rule) {
          _pacc->err_valid = 0;
          _pacc_error(_pacc, ".Simple", _x_rule);
        }
      }
      goto contin;
      case 666: /* First */
      PACC_TRACE fprintf(stderr, "rule 666 (First) col %ld\n", _x);
      _x_rule = _x;
      cur = _pacc_result(_pacc, _x, 666);
      if ((cur->rule & 3) == uncomputed) {
        PACC_TRACE fprintf(stderr, "seq 664 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 664;
        _status = parsed;
        /* bind: c */
        PACC_TRACE fprintf(stderr, "bind 656 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind c @ rule 826, col %ld\n", _x);
        _pacc_save_core(826, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 655;
        _st = 826;
        /* call comword */
        goto top;
        case 655: /* return from comword */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 666);
        /* end bind: c */
        if (_status == no_parse) {
          goto contin;
        }
        _pacc_save_core(978, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 660;
        _st = 978;
        /* call First:*:0 */
        goto top;
        case 660: /* return from First:*:0 */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 666);
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "expr 663 @ col %ld?\n", _x);
        assert(cur->expr_id == 0);
        cur->expr_id = 663;
        case 663:
        if (_evaling) {
          struct pacc_mid *_pacc_p;
          /* i is 0, type is struct Node * */
          struct Node * c;
          PACC_TRACE fprintf(stderr, "663: evaluating\n");
          _pacc_p = cur = _pacc_result(_pacc, _x, 666);
          _pos = 0;
          PACC_TRACE fprintf(stderr, "binding of c: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind c to r826 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 826);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 661;
            _pacc_ev_i = 0; goto eval_loop;
            case 661:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          c = cur->value.u3;
          PACC_TRACE fprintf(stderr, "bound c to r826 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          cur = _pacc_p;
          cur->value.u3=
#line 144 "parse.pacc"
                                (c)
#line 6020 "parse.c"
          ;
          PACC_TRACE fprintf(stderr, "stash " TYPE_PRINTF " to (%ld, 666)\n", cur->value.u0, _x);
          goto _pacc_expr_done;
        }
        case 664:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 664 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        cur->rule = (cur->rule & ~3) | _status;
        cur->remainder = _x;
        if (_pacc->err_col == _x_rule) {
          _pacc->err_valid = 0;
          _pacc_error(_pacc, ".First", _x_rule);
        }
      }
      goto contin;
      case 674: /* sword */
      PACC_TRACE fprintf(stderr, "rule 674 (sword) col %ld\n", _x);
      _x_rule = _x;
      cur = _pacc_result(_pacc, _x, 674);
      if ((cur->rule & 3) == uncomputed) {
        PACC_TRACE fprintf(stderr, "seq 672 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 672;
        _status = parsed;
        /* bind: c */
        PACC_TRACE fprintf(stderr, "bind 668 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind c @ rule 826, col %ld\n", _x);
        _pacc_save_core(826, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 667;
        _st = 826;
        /* call comword */
        goto top;
        case 667: /* return from comword */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 674);
        /* end bind: c */
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "expr 671 @ col %ld?\n", _x);
        assert(cur->expr_id == 0);
        cur->expr_id = 671;
        case 671:
        if (_evaling) {
          struct pacc_mid *_pacc_p;
          /* i is 0, type is struct Node * */
          struct Node * c;
          PACC_TRACE fprintf(stderr, "671: evaluating\n");
          _pacc_p = cur = _pacc_result(_pacc, _x, 674);
          _pos = 0;
          PACC_TRACE fprintf(stderr, "binding of c: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind c to r826 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 826);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 669;
            _pacc_ev_i = 0; goto eval_loop;
            case 669:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          c = cur->value.u3;
          PACC_TRACE fprintf(stderr, "bound c to r826 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          cur = _pacc_p;
          cur->value.u3=
#line 146 "parse.pacc"
                   (c)
#line 6093 "parse.c"
          ;
          PACC_TRACE fprintf(stderr, "stash " TYPE_PRINTF " to (%ld, 674)\n", cur->value.u0, _x);
          goto _pacc_expr_done;
        }
        case 672:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 672 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        cur->rule = (cur->rule & ~3) | _status;
        cur->remainder = _x;
        if (_pacc->err_col == _x_rule) {
          _pacc->err_valid = 0;
          _pacc_error(_pacc, ".sword", _x_rule);
        }
      }
      goto contin;
      case 695: /* word */
      PACC_TRACE fprintf(stderr, "rule 695 (word) col %ld\n", _x);
      _x_rule = _x;
      cur = _pacc_result(_pacc, _x, 695);
      if ((cur->rule & 3) == uncomputed) {
        PACC_TRACE fprintf(stderr, "alt 693 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 693;
        PACC_TRACE fprintf(stderr, "save column registers\n");
        _pacc_Push(_x); _pacc_Push(cur->ev_valid);
        PACC_TRACE fprintf(stderr, "seq 680 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 680;
        _status = parsed;
        /* bind: w */
        PACC_TRACE fprintf(stderr, "bind 676 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind w @ rule 674, col %ld\n", _x);
        _pacc_save_core(674, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 675;
        _st = 674;
        /* call sword */
        goto top;
        case 675: /* return from sword */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 695);
        /* end bind: w */
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "expr 679 @ col %ld?\n", _x);
        assert(cur->expr_id == 0);
        cur->expr_id = 679;
        case 679:
        if (_evaling) {
          struct pacc_mid *_pacc_p;
          /* i is 0, type is struct Node * */
          struct Node * w;
          PACC_TRACE fprintf(stderr, "679: evaluating\n");
          _pacc_p = cur = _pacc_result(_pacc, _x, 695);
          _pos = 0;
          PACC_TRACE fprintf(stderr, "binding of w: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind w to r674 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 674);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 677;
            _pacc_ev_i = 0; goto eval_loop;
            case 677:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          w = cur->value.u3;
          PACC_TRACE fprintf(stderr, "bound w to r674 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          cur = _pacc_p;
          cur->value.u3=
#line 149 "parse.pacc"
                (w)
#line 6171 "parse.c"
          ;
          PACC_TRACE fprintf(stderr, "stash " TYPE_PRINTF " to (%ld, 695)\n", cur->value.u0, _x);
          goto _pacc_expr_done;
        }
        case 680:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 680 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 693 @ col %ld => %s\n", _x, _status!=no_parse?"yes":"no");
        if (_status != no_parse) {
          PACC_TRACE fprintf(stderr, "accept column registers\n");
          _pacc_Discard(cur->ev_valid); _pacc_Discard(_x);
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "restore column registers\n");
        _pacc_Pop(cur->ev_valid); _pacc_Pop(_x);
        PACC_TRACE fprintf(stderr, "save column registers\n");
        _pacc_Push(_x); _pacc_Push(cur->ev_valid);
        PACC_TRACE fprintf(stderr, "col restored to %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 693 @ col %ld? (next alternative)\n", _x);
        PACC_TRACE fprintf(stderr, "seq 692 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 692;
        _status = parsed;
        /* bind: a */
        PACC_TRACE fprintf(stderr, "bind 682 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind a @ rule 674, col %ld\n", _x);
        _pacc_save_core(674, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 681;
        _st = 674;
        /* call sword */
        goto top;
        case 681: /* return from sword */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 695);
        /* end bind: a */
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "lit 683 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "lit 683 @ col %ld => ", _x);
        if (_x+1 <= _pacc->input_length && memcmp("^", _pacc->string + _x, 1) == 0) {
          _status = parsed;
          _x += 1;
        }
        else {
          _pacc_error(_pacc, ".\"^\"", _x);
          _status = no_parse;
        }
        PACC_TRACE fprintf(stderr, "lit 683 %ld => %s\n", _x, _status != no_parse ? "yes" : "no");
        if (_status == no_parse) {
          goto contin;
        }
        /* bind: b */
        PACC_TRACE fprintf(stderr, "bind 685 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind b @ rule 695, col %ld\n", _x);
        _pacc_save_core(695, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 684;
        _st = 695;
        /* call word */
        goto top;
        case 684: /* return from word */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 695);
        /* end bind: b */
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "expr 691 @ col %ld?\n", _x);
        assert(cur->expr_id == 0);
        cur->expr_id = 691;
        case 691:
        if (_evaling) {
          struct pacc_mid *_pacc_p;
          /* i is 0, type is struct Node * */
          struct Node * a;
          /* i is 1, type is struct Node * */
          struct Node * b;
          PACC_TRACE fprintf(stderr, "691: evaluating\n");
          _pacc_p = cur = _pacc_result(_pacc, _x, 695);
          _pos = 0;
          PACC_TRACE fprintf(stderr, "binding of a: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind a to r674 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 674);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 687;
            _pacc_ev_i = 0; goto eval_loop;
            case 687:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          a = cur->value.u3;
          PACC_TRACE fprintf(stderr, "bound a to r674 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          _pos = 1;
          PACC_TRACE fprintf(stderr, "binding of b: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind b to r695 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 695);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 686;
            _pacc_ev_i = 0; goto eval_loop;
            case 686:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          b = cur->value.u3;
          PACC_TRACE fprintf(stderr, "bound b to r695 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          cur = _pacc_p;
          cur->value.u3=
#line 150 "parse.pacc"
                       ( mk(nConcat, a, b) )
#line 6292 "parse.c"
          ;
          PACC_TRACE fprintf(stderr, "stash " TYPE_PRINTF " to (%ld, 695)\n", cur->value.u0, _x);
          goto _pacc_expr_done;
        }
        case 692:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 692 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        if (_status == no_parse) {
          PACC_TRACE fprintf(stderr, "restore column registers\n");
          _pacc_Pop(cur->ev_valid); _pacc_Pop(_x);
        }
        else {
          PACC_TRACE fprintf(stderr, "accept column registers\n");
          _pacc_Discard(cur->ev_valid); _pacc_Discard(_x);
        }
        case 693:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "alt 693 @ col %ld => %s\n", _x, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        cur->rule = (cur->rule & ~3) | _status;
        cur->remainder = _x;
        if (_pacc->err_col == _x_rule) {
          _pacc->err_valid = 0;
          _pacc_error(_pacc, ".word", _x_rule);
        }
      }
      goto contin;
      case 826: /* comword */
      PACC_TRACE fprintf(stderr, "rule 826 (comword) col %ld\n", _x);
      _x_rule = _x;
      cur = _pacc_result(_pacc, _x, 826);
      if ((cur->rule & 3) == uncomputed) {
        PACC_TRACE fprintf(stderr, "alt 824 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 824;
        PACC_TRACE fprintf(stderr, "save column registers\n");
        _pacc_Push(_x); _pacc_Push(cur->ev_valid);
        PACC_TRACE fprintf(stderr, "seq 704 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 704;
        _status = parsed;
        PACC_TRACE fprintf(stderr, "lit 696 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "lit 696 @ col %ld => ", _x);
        if (_x+1 <= _pacc->input_length && memcmp("$", _pacc->string + _x, 1) == 0) {
          _status = parsed;
          _x += 1;
        }
        else {
          _pacc_error(_pacc, ".\"$\"", _x);
          _status = no_parse;
        }
        PACC_TRACE fprintf(stderr, "lit 696 %ld => %s\n", _x, _status != no_parse ? "yes" : "no");
        if (_status == no_parse) {
          goto contin;
        }
        /* bind: s */
        PACC_TRACE fprintf(stderr, "bind 698 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind s @ rule 674, col %ld\n", _x);
        _pacc_save_core(674, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 697;
        _st = 674;
        /* call sword */
        goto top;
        case 697: /* return from sword */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 826);
        /* end bind: s */
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "expr 703 @ col %ld?\n", _x);
        assert(cur->expr_id == 0);
        cur->expr_id = 703;
        case 703:
        if (_evaling) {
          struct pacc_mid *_pacc_p;
          /* i is 0, type is struct Node * */
          struct Node * s;
          PACC_TRACE fprintf(stderr, "703: evaluating\n");
          _pacc_p = cur = _pacc_result(_pacc, _x, 826);
          _pos = 0;
          PACC_TRACE fprintf(stderr, "binding of s: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind s to r674 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 674);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 699;
            _pacc_ev_i = 0; goto eval_loop;
            case 699:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          s = cur->value.u3;
          PACC_TRACE fprintf(stderr, "bound s to r674 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          cur = _pacc_p;
          cur->value.u3=
#line 166 "parse.pacc"
                        ( mk(nVar, s) )
#line 6396 "parse.c"
          ;
          PACC_TRACE fprintf(stderr, "stash " TYPE_PRINTF " to (%ld, 826)\n", cur->value.u0, _x);
          goto _pacc_expr_done;
        }
        case 704:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 704 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 824 @ col %ld => %s\n", _x, _status!=no_parse?"yes":"no");
        if (_status != no_parse) {
          PACC_TRACE fprintf(stderr, "accept column registers\n");
          _pacc_Discard(cur->ev_valid); _pacc_Discard(_x);
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "restore column registers\n");
        _pacc_Pop(cur->ev_valid); _pacc_Pop(_x);
        PACC_TRACE fprintf(stderr, "save column registers\n");
        _pacc_Push(_x); _pacc_Push(cur->ev_valid);
        PACC_TRACE fprintf(stderr, "col restored to %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 824 @ col %ld? (next alternative)\n", _x);
        PACC_TRACE fprintf(stderr, "seq 718 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 718;
        _status = parsed;
        PACC_TRACE fprintf(stderr, "lit 705 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "lit 705 @ col %ld => ", _x);
        if (_x+1 <= _pacc->input_length && memcmp("$", _pacc->string + _x, 1) == 0) {
          _status = parsed;
          _x += 1;
        }
        else {
          _pacc_error(_pacc, ".\"$\"", _x);
          _status = no_parse;
        }
        PACC_TRACE fprintf(stderr, "lit 705 %ld => %s\n", _x, _status != no_parse ? "yes" : "no");
        if (_status == no_parse) {
          goto contin;
        }
        /* bind: s */
        PACC_TRACE fprintf(stderr, "bind 707 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind s @ rule 674, col %ld\n", _x);
        _pacc_save_core(674, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 706;
        _st = 674;
        /* call sword */
        goto top;
        case 706: /* return from sword */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 826);
        /* end bind: s */
        if (_status == no_parse) {
          goto contin;
        }
        _pacc_save_core(911, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 708;
        _st = 911;
        /* call lParen */
        goto top;
        case 708: /* return from lParen */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 826);
        if (_status == no_parse) {
          goto contin;
        }
        /* bind: ws */
        PACC_TRACE fprintf(stderr, "bind 710 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind ws @ rule 843, col %ld\n", _x);
        _pacc_save_core(843, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 709;
        _st = 843;
        /* call Words */
        goto top;
        case 709: /* return from Words */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 826);
        /* end bind: ws */
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "lit 711 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "lit 711 @ col %ld => ", _x);
        if (_x+1 <= _pacc->input_length && memcmp(")", _pacc->string + _x, 1) == 0) {
          _status = parsed;
          _x += 1;
        }
        else {
          _pacc_error(_pacc, ".\")\"", _x);
          _status = no_parse;
        }
        PACC_TRACE fprintf(stderr, "lit 711 %ld => %s\n", _x, _status != no_parse ? "yes" : "no");
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "expr 717 @ col %ld?\n", _x);
        assert(cur->expr_id == 0);
        cur->expr_id = 717;
        case 717:
        if (_evaling) {
          struct pacc_mid *_pacc_p;
          /* i is 0, type is struct Node * */
          struct Node * s;
          /* i is 2, type is struct Node * */
          struct Node * ws;
          PACC_TRACE fprintf(stderr, "717: evaluating\n");
          _pacc_p = cur = _pacc_result(_pacc, _x, 826);
          _pos = 0;
          PACC_TRACE fprintf(stderr, "binding of s: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind s to r674 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 674);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 713;
            _pacc_ev_i = 0; goto eval_loop;
            case 713:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          s = cur->value.u3;
          PACC_TRACE fprintf(stderr, "bound s to r674 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          _pos = 2;
          PACC_TRACE fprintf(stderr, "binding of ws: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind ws to r843 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 843);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 712;
            _pacc_ev_i = 0; goto eval_loop;
            case 712:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          ws = cur->value.u3;
          PACC_TRACE fprintf(stderr, "bound ws to r843 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          cur = _pacc_p;
          cur->value.u3=
#line 167 "parse.pacc"
                                   ( mk(nVarsub, s, ws) )
#line 6547 "parse.c"
          ;
          PACC_TRACE fprintf(stderr, "stash " TYPE_PRINTF " to (%ld, 826)\n", cur->value.u0, _x);
          goto _pacc_expr_done;
        }
        case 718:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 718 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 824 @ col %ld => %s\n", _x, _status!=no_parse?"yes":"no");
        if (_status != no_parse) {
          PACC_TRACE fprintf(stderr, "accept column registers\n");
          _pacc_Discard(cur->ev_valid); _pacc_Discard(_x);
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "restore column registers\n");
        _pacc_Pop(cur->ev_valid); _pacc_Pop(_x);
        PACC_TRACE fprintf(stderr, "save column registers\n");
        _pacc_Push(_x); _pacc_Push(cur->ev_valid);
        PACC_TRACE fprintf(stderr, "col restored to %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 824 @ col %ld? (next alternative)\n", _x);
        PACC_TRACE fprintf(stderr, "seq 727 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 727;
        _status = parsed;
        PACC_TRACE fprintf(stderr, "lit 719 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "lit 719 @ col %ld => ", _x);
        if (_x+2 <= _pacc->input_length && memcmp("$#", _pacc->string + _x, 2) == 0) {
          _status = parsed;
          _x += 2;
        }
        else {
          _pacc_error(_pacc, ".\"$#\"", _x);
          _status = no_parse;
        }
        PACC_TRACE fprintf(stderr, "lit 719 %ld => %s\n", _x, _status != no_parse ? "yes" : "no");
        if (_status == no_parse) {
          goto contin;
        }
        /* bind: s */
        PACC_TRACE fprintf(stderr, "bind 721 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind s @ rule 674, col %ld\n", _x);
        _pacc_save_core(674, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 720;
        _st = 674;
        /* call sword */
        goto top;
        case 720: /* return from sword */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 826);
        /* end bind: s */
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "expr 726 @ col %ld?\n", _x);
        assert(cur->expr_id == 0);
        cur->expr_id = 726;
        case 726:
        if (_evaling) {
          struct pacc_mid *_pacc_p;
          /* i is 0, type is struct Node * */
          struct Node * s;
          PACC_TRACE fprintf(stderr, "726: evaluating\n");
          _pacc_p = cur = _pacc_result(_pacc, _x, 826);
          _pos = 0;
          PACC_TRACE fprintf(stderr, "binding of s: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind s to r674 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 674);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 722;
            _pacc_ev_i = 0; goto eval_loop;
            case 722:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          s = cur->value.u3;
          PACC_TRACE fprintf(stderr, "bound s to r674 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          cur = _pacc_p;
          cur->value.u3=
#line 168 "parse.pacc"
                  ( mk(nCount, s) )
#line 6633 "parse.c"
          ;
          PACC_TRACE fprintf(stderr, "stash " TYPE_PRINTF " to (%ld, 826)\n", cur->value.u0, _x);
          goto _pacc_expr_done;
        }
        case 727:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 727 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 824 @ col %ld => %s\n", _x, _status!=no_parse?"yes":"no");
        if (_status != no_parse) {
          PACC_TRACE fprintf(stderr, "accept column registers\n");
          _pacc_Discard(cur->ev_valid); _pacc_Discard(_x);
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "restore column registers\n");
        _pacc_Pop(cur->ev_valid); _pacc_Pop(_x);
        PACC_TRACE fprintf(stderr, "save column registers\n");
        _pacc_Push(_x); _pacc_Push(cur->ev_valid);
        PACC_TRACE fprintf(stderr, "col restored to %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 824 @ col %ld? (next alternative)\n", _x);
        PACC_TRACE fprintf(stderr, "seq 736 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 736;
        _status = parsed;
        PACC_TRACE fprintf(stderr, "lit 728 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "lit 728 @ col %ld => ", _x);
        if (_x+2 <= _pacc->input_length && memcmp("$^", _pacc->string + _x, 2) == 0) {
          _status = parsed;
          _x += 2;
        }
        else {
          _pacc_error(_pacc, ".\"$^\"", _x);
          _status = no_parse;
        }
        PACC_TRACE fprintf(stderr, "lit 728 %ld => %s\n", _x, _status != no_parse ? "yes" : "no");
        if (_status == no_parse) {
          goto contin;
        }
        /* bind: s */
        PACC_TRACE fprintf(stderr, "bind 730 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind s @ rule 674, col %ld\n", _x);
        _pacc_save_core(674, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 729;
        _st = 674;
        /* call sword */
        goto top;
        case 729: /* return from sword */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 826);
        /* end bind: s */
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "expr 735 @ col %ld?\n", _x);
        assert(cur->expr_id == 0);
        cur->expr_id = 735;
        case 735:
        if (_evaling) {
          struct pacc_mid *_pacc_p;
          /* i is 0, type is struct Node * */
          struct Node * s;
          PACC_TRACE fprintf(stderr, "735: evaluating\n");
          _pacc_p = cur = _pacc_result(_pacc, _x, 826);
          _pos = 0;
          PACC_TRACE fprintf(stderr, "binding of s: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind s to r674 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 674);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 731;
            _pacc_ev_i = 0; goto eval_loop;
            case 731:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          s = cur->value.u3;
          PACC_TRACE fprintf(stderr, "bound s to r674 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          cur = _pacc_p;
          cur->value.u3=
#line 169 "parse.pacc"
                  ( mk(nFlat,  s) )
#line 6719 "parse.c"
          ;
          PACC_TRACE fprintf(stderr, "stash " TYPE_PRINTF " to (%ld, 826)\n", cur->value.u0, _x);
          goto _pacc_expr_done;
        }
        case 736:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 736 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 824 @ col %ld => %s\n", _x, _status!=no_parse?"yes":"no");
        if (_status != no_parse) {
          PACC_TRACE fprintf(stderr, "accept column registers\n");
          _pacc_Discard(cur->ev_valid); _pacc_Discard(_x);
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "restore column registers\n");
        _pacc_Pop(cur->ev_valid); _pacc_Pop(_x);
        PACC_TRACE fprintf(stderr, "save column registers\n");
        _pacc_Push(_x); _pacc_Push(cur->ev_valid);
        PACC_TRACE fprintf(stderr, "col restored to %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 824 @ col %ld? (next alternative)\n", _x);
        PACC_TRACE fprintf(stderr, "seq 746 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 746;
        _status = parsed;
        PACC_TRACE fprintf(stderr, "lit 737 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "lit 737 @ col %ld => ", _x);
        if (_x+1 <= _pacc->input_length && memcmp("`", _pacc->string + _x, 1) == 0) {
          _status = parsed;
          _x += 1;
        }
        else {
          _pacc_error(_pacc, ".\"`\"", _x);
          _status = no_parse;
        }
        PACC_TRACE fprintf(stderr, "lit 737 %ld => %s\n", _x, _status != no_parse ? "yes" : "no");
        if (_status == no_parse) {
          goto contin;
        }
        /* bind: s */
        PACC_TRACE fprintf(stderr, "bind 739 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind s @ rule 674, col %ld\n", _x);
        _pacc_save_core(674, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 738;
        _st = 674;
        /* call sword */
        goto top;
        case 738: /* return from sword */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 826);
        /* end bind: s */
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "expr 745 @ col %ld?\n", _x);
        assert(cur->expr_id == 0);
        cur->expr_id = 745;
        case 745:
        if (_evaling) {
          struct pacc_mid *_pacc_p;
          /* i is 0, type is struct Node * */
          struct Node * s;
          PACC_TRACE fprintf(stderr, "745: evaluating\n");
          _pacc_p = cur = _pacc_result(_pacc, _x, 826);
          _pos = 0;
          PACC_TRACE fprintf(stderr, "binding of s: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind s to r674 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 674);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 740;
            _pacc_ev_i = 0; goto eval_loop;
            case 740:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          s = cur->value.u3;
          PACC_TRACE fprintf(stderr, "bound s to r674 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          cur = _pacc_p;
          cur->value.u3=
#line 170 "parse.pacc"
                 ( mk(nBackq,nolist, s) )
#line 6805 "parse.c"
          ;
          PACC_TRACE fprintf(stderr, "stash " TYPE_PRINTF " to (%ld, 826)\n", cur->value.u0, _x);
          goto _pacc_expr_done;
        }
        case 746:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 746 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 824 @ col %ld => %s\n", _x, _status!=no_parse?"yes":"no");
        if (_status != no_parse) {
          PACC_TRACE fprintf(stderr, "accept column registers\n");
          _pacc_Discard(cur->ev_valid); _pacc_Discard(_x);
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "restore column registers\n");
        _pacc_Pop(cur->ev_valid); _pacc_Pop(_x);
        PACC_TRACE fprintf(stderr, "save column registers\n");
        _pacc_Push(_x); _pacc_Push(cur->ev_valid);
        PACC_TRACE fprintf(stderr, "col restored to %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 824 @ col %ld? (next alternative)\n", _x);
        PACC_TRACE fprintf(stderr, "seq 756 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 756;
        _status = parsed;
        PACC_TRACE fprintf(stderr, "lit 747 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "lit 747 @ col %ld => ", _x);
        if (_x+1 <= _pacc->input_length && memcmp("`", _pacc->string + _x, 1) == 0) {
          _status = parsed;
          _x += 1;
        }
        else {
          _pacc_error(_pacc, ".\"`\"", _x);
          _status = no_parse;
        }
        PACC_TRACE fprintf(stderr, "lit 747 %ld => %s\n", _x, _status != no_parse ? "yes" : "no");
        if (_status == no_parse) {
          goto contin;
        }
        /* bind: b */
        PACC_TRACE fprintf(stderr, "bind 749 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind b @ rule 221, col %ld\n", _x);
        _pacc_save_core(221, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 748;
        _st = 221;
        /* call brace */
        goto top;
        case 748: /* return from brace */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 826);
        /* end bind: b */
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "expr 755 @ col %ld?\n", _x);
        assert(cur->expr_id == 0);
        cur->expr_id = 755;
        case 755:
        if (_evaling) {
          struct pacc_mid *_pacc_p;
          /* i is 0, type is Node * */
          Node * b;
          PACC_TRACE fprintf(stderr, "755: evaluating\n");
          _pacc_p = cur = _pacc_result(_pacc, _x, 826);
          _pos = 0;
          PACC_TRACE fprintf(stderr, "binding of b: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind b to r221 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 221);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 750;
            _pacc_ev_i = 0; goto eval_loop;
            case 750:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          b = cur->value.u0;
          PACC_TRACE fprintf(stderr, "bound b to r221 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          cur = _pacc_p;
          cur->value.u3=
#line 171 "parse.pacc"
                 ( mk(nBackq,nolist, b) )
#line 6891 "parse.c"
          ;
          PACC_TRACE fprintf(stderr, "stash " TYPE_PRINTF " to (%ld, 826)\n", cur->value.u0, _x);
          goto _pacc_expr_done;
        }
        case 756:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 756 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 824 @ col %ld => %s\n", _x, _status!=no_parse?"yes":"no");
        if (_status != no_parse) {
          PACC_TRACE fprintf(stderr, "accept column registers\n");
          _pacc_Discard(cur->ev_valid); _pacc_Discard(_x);
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "restore column registers\n");
        _pacc_Pop(cur->ev_valid); _pacc_Pop(_x);
        PACC_TRACE fprintf(stderr, "save column registers\n");
        _pacc_Push(_x); _pacc_Push(cur->ev_valid);
        PACC_TRACE fprintf(stderr, "col restored to %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 824 @ col %ld? (next alternative)\n", _x);
        PACC_TRACE fprintf(stderr, "seq 768 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 768;
        _status = parsed;
        PACC_TRACE fprintf(stderr, "lit 757 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "lit 757 @ col %ld => ", _x);
        if (_x+2 <= _pacc->input_length && memcmp("``", _pacc->string + _x, 2) == 0) {
          _status = parsed;
          _x += 2;
        }
        else {
          _pacc_error(_pacc, ".\"``\"", _x);
          _status = no_parse;
        }
        PACC_TRACE fprintf(stderr, "lit 757 %ld => %s\n", _x, _status != no_parse ? "yes" : "no");
        if (_status == no_parse) {
          goto contin;
        }
        /* bind: a */
        PACC_TRACE fprintf(stderr, "bind 759 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind a @ rule 695, col %ld\n", _x);
        _pacc_save_core(695, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 758;
        _st = 695;
        /* call word */
        goto top;
        case 758: /* return from word */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 826);
        /* end bind: a */
        if (_status == no_parse) {
          goto contin;
        }
        /* bind: b */
        PACC_TRACE fprintf(stderr, "bind 761 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind b @ rule 221, col %ld\n", _x);
        _pacc_save_core(221, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 760;
        _st = 221;
        /* call brace */
        goto top;
        case 760: /* return from brace */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 826);
        /* end bind: b */
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "expr 767 @ col %ld?\n", _x);
        assert(cur->expr_id == 0);
        cur->expr_id = 767;
        case 767:
        if (_evaling) {
          struct pacc_mid *_pacc_p;
          /* i is 0, type is struct Node * */
          struct Node * a;
          /* i is 1, type is Node * */
          Node * b;
          PACC_TRACE fprintf(stderr, "767: evaluating\n");
          _pacc_p = cur = _pacc_result(_pacc, _x, 826);
          _pos = 0;
          PACC_TRACE fprintf(stderr, "binding of a: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind a to r695 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 695);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 763;
            _pacc_ev_i = 0; goto eval_loop;
            case 763:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          a = cur->value.u3;
          PACC_TRACE fprintf(stderr, "bound a to r695 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          _pos = 1;
          PACC_TRACE fprintf(stderr, "binding of b: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind b to r221 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 221);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 762;
            _pacc_ev_i = 0; goto eval_loop;
            case 762:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          b = cur->value.u0;
          PACC_TRACE fprintf(stderr, "bound b to r221 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          cur = _pacc_p;
          cur->value.u3=
#line 172 "parse.pacc"
                        ( mk(nBackq, a, b) )
#line 7012 "parse.c"
          ;
          PACC_TRACE fprintf(stderr, "stash " TYPE_PRINTF " to (%ld, 826)\n", cur->value.u0, _x);
          goto _pacc_expr_done;
        }
        case 768:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 768 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 824 @ col %ld => %s\n", _x, _status!=no_parse?"yes":"no");
        if (_status != no_parse) {
          PACC_TRACE fprintf(stderr, "accept column registers\n");
          _pacc_Discard(cur->ev_valid); _pacc_Discard(_x);
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "restore column registers\n");
        _pacc_Pop(cur->ev_valid); _pacc_Pop(_x);
        PACC_TRACE fprintf(stderr, "save column registers\n");
        _pacc_Push(_x); _pacc_Push(cur->ev_valid);
        PACC_TRACE fprintf(stderr, "col restored to %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 824 @ col %ld? (next alternative)\n", _x);
        PACC_TRACE fprintf(stderr, "seq 780 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 780;
        _status = parsed;
        PACC_TRACE fprintf(stderr, "lit 769 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "lit 769 @ col %ld => ", _x);
        if (_x+2 <= _pacc->input_length && memcmp("``", _pacc->string + _x, 2) == 0) {
          _status = parsed;
          _x += 2;
        }
        else {
          _pacc_error(_pacc, ".\"``\"", _x);
          _status = no_parse;
        }
        PACC_TRACE fprintf(stderr, "lit 769 %ld => %s\n", _x, _status != no_parse ? "yes" : "no");
        if (_status == no_parse) {
          goto contin;
        }
        /* bind: a */
        PACC_TRACE fprintf(stderr, "bind 771 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind a @ rule 695, col %ld\n", _x);
        _pacc_save_core(695, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 770;
        _st = 695;
        /* call word */
        goto top;
        case 770: /* return from word */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 826);
        /* end bind: a */
        if (_status == no_parse) {
          goto contin;
        }
        /* bind: b */
        PACC_TRACE fprintf(stderr, "bind 773 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind b @ rule 674, col %ld\n", _x);
        _pacc_save_core(674, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 772;
        _st = 674;
        /* call sword */
        goto top;
        case 772: /* return from sword */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 826);
        /* end bind: b */
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "expr 779 @ col %ld?\n", _x);
        assert(cur->expr_id == 0);
        cur->expr_id = 779;
        case 779:
        if (_evaling) {
          struct pacc_mid *_pacc_p;
          /* i is 0, type is struct Node * */
          struct Node * a;
          /* i is 1, type is struct Node * */
          struct Node * b;
          PACC_TRACE fprintf(stderr, "779: evaluating\n");
          _pacc_p = cur = _pacc_result(_pacc, _x, 826);
          _pos = 0;
          PACC_TRACE fprintf(stderr, "binding of a: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind a to r695 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 695);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 775;
            _pacc_ev_i = 0; goto eval_loop;
            case 775:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          a = cur->value.u3;
          PACC_TRACE fprintf(stderr, "bound a to r695 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          _pos = 1;
          PACC_TRACE fprintf(stderr, "binding of b: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind b to r674 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 674);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 774;
            _pacc_ev_i = 0; goto eval_loop;
            case 774:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          b = cur->value.u3;
          PACC_TRACE fprintf(stderr, "bound b to r674 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          cur = _pacc_p;
          cur->value.u3=
#line 173 "parse.pacc"
                        ( mk(nBackq, a, b) )
#line 7133 "parse.c"
          ;
          PACC_TRACE fprintf(stderr, "stash " TYPE_PRINTF " to (%ld, 826)\n", cur->value.u0, _x);
          goto _pacc_expr_done;
        }
        case 780:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 780 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 824 @ col %ld => %s\n", _x, _status!=no_parse?"yes":"no");
        if (_status != no_parse) {
          PACC_TRACE fprintf(stderr, "accept column registers\n");
          _pacc_Discard(cur->ev_valid); _pacc_Discard(_x);
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "restore column registers\n");
        _pacc_Pop(cur->ev_valid); _pacc_Pop(_x);
        PACC_TRACE fprintf(stderr, "save column registers\n");
        _pacc_Push(_x); _pacc_Push(cur->ev_valid);
        PACC_TRACE fprintf(stderr, "col restored to %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 824 @ col %ld? (next alternative)\n", _x);
        PACC_TRACE fprintf(stderr, "seq 788 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 788;
        _status = parsed;
        PACC_TRACE fprintf(stderr, "lit 781 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "lit 781 @ col %ld => ", _x);
        if (_x+1 <= _pacc->input_length && memcmp("(", _pacc->string + _x, 1) == 0) {
          _status = parsed;
          _x += 1;
        }
        else {
          _pacc_error(_pacc, ".\"(\"", _x);
          _status = no_parse;
        }
        PACC_TRACE fprintf(stderr, "lit 781 %ld => %s\n", _x, _status != no_parse ? "yes" : "no");
        if (_status == no_parse) {
          goto contin;
        }
        /* bind: ws */
        PACC_TRACE fprintf(stderr, "bind 783 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind ws @ rule 875, col %ld\n", _x);
        _pacc_save_core(875, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 782;
        _st = 875;
        /* call nlwords */
        goto top;
        case 782: /* return from nlwords */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 826);
        /* end bind: ws */
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "lit 784 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "lit 784 @ col %ld => ", _x);
        if (_x+1 <= _pacc->input_length && memcmp(")", _pacc->string + _x, 1) == 0) {
          _status = parsed;
          _x += 1;
        }
        else {
          _pacc_error(_pacc, ".\")\"", _x);
          _status = no_parse;
        }
        PACC_TRACE fprintf(stderr, "lit 784 %ld => %s\n", _x, _status != no_parse ? "yes" : "no");
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "expr 787 @ col %ld?\n", _x);
        assert(cur->expr_id == 0);
        cur->expr_id = 787;
        case 787:
        if (_evaling) {
          struct pacc_mid *_pacc_p;
          /* i is 0, type is struct Node * */
          struct Node * ws;
          PACC_TRACE fprintf(stderr, "787: evaluating\n");
          _pacc_p = cur = _pacc_result(_pacc, _x, 826);
          _pos = 0;
          PACC_TRACE fprintf(stderr, "binding of ws: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind ws to r875 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 875);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 785;
            _pacc_ev_i = 0; goto eval_loop;
            case 785:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          ws = cur->value.u3;
          PACC_TRACE fprintf(stderr, "bound ws to r875 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          cur = _pacc_p;
          cur->value.u3=
#line 174 "parse.pacc"
                       ( ws )
#line 7233 "parse.c"
          ;
          PACC_TRACE fprintf(stderr, "stash " TYPE_PRINTF " to (%ld, 826)\n", cur->value.u0, _x);
          goto _pacc_expr_done;
        }
        case 788:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 788 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 824 @ col %ld => %s\n", _x, _status!=no_parse?"yes":"no");
        if (_status != no_parse) {
          PACC_TRACE fprintf(stderr, "accept column registers\n");
          _pacc_Discard(cur->ev_valid); _pacc_Discard(_x);
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "restore column registers\n");
        _pacc_Pop(cur->ev_valid); _pacc_Pop(_x);
        PACC_TRACE fprintf(stderr, "save column registers\n");
        _pacc_Push(_x); _pacc_Push(cur->ev_valid);
        PACC_TRACE fprintf(stderr, "col restored to %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 824 @ col %ld? (next alternative)\n", _x);
        PACC_TRACE fprintf(stderr, "seq 804 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 804;
        _status = parsed;
        /* bind: r */
        PACC_TRACE fprintf(stderr, "bind 790 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind r @ rule 298, col %ld\n", _x);
        _pacc_save_core(298, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 789;
        _st = 298;
        /* call redir */
        goto top;
        case 789: /* return from redir */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 826);
        /* end bind: r */
        if (_status == no_parse) {
          goto contin;
        }
        /* bind: b */
        PACC_TRACE fprintf(stderr, "bind 792 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind b @ rule 221, col %ld\n", _x);
        _pacc_save_core(221, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 791;
        _st = 221;
        /* call brace */
        goto top;
        case 791: /* return from brace */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 826);
        /* end bind: b */
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "expr 803 @ col %ld?\n", _x);
        assert(cur->expr_id == 0);
        cur->expr_id = 803;
        case 803:
        if (_evaling) {
          struct pacc_mid *_pacc_p;
          /* i is 0, type is Node * */
          Node * r;
          /* i is 1, type is Node * */
          Node * b;
          PACC_TRACE fprintf(stderr, "803: evaluating\n");
          _pacc_p = cur = _pacc_result(_pacc, _x, 826);
          _pos = 0;
          PACC_TRACE fprintf(stderr, "binding of r: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind r to r298 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 298);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 795;
            _pacc_ev_i = 0; goto eval_loop;
            case 795:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          r = cur->value.u0;
          PACC_TRACE fprintf(stderr, "bound r to r298 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          _pos = 1;
          PACC_TRACE fprintf(stderr, "binding of b: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind b to r221 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 221);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 793;
            _pacc_ev_i = 0; goto eval_loop;
            case 793:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          b = cur->value.u0;
          PACC_TRACE fprintf(stderr, "bound b to r221 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          cur = _pacc_p;
          cur->value.u3=
#line 175 "parse.pacc"
                    ( mk(nNmpipe, r->type, ((struct Redir *)r)->fd, b) )
#line 7340 "parse.c"
          ;
          PACC_TRACE fprintf(stderr, "stash " TYPE_PRINTF " to (%ld, 826)\n", cur->value.u0, _x);
          goto _pacc_expr_done;
        }
        case 804:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 804 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 824 @ col %ld => %s\n", _x, _status!=no_parse?"yes":"no");
        if (_status != no_parse) {
          PACC_TRACE fprintf(stderr, "accept column registers\n");
          _pacc_Discard(cur->ev_valid); _pacc_Discard(_x);
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "restore column registers\n");
        _pacc_Pop(cur->ev_valid); _pacc_Pop(_x);
        PACC_TRACE fprintf(stderr, "save column registers\n");
        _pacc_Push(_x); _pacc_Push(cur->ev_valid);
        PACC_TRACE fprintf(stderr, "col restored to %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 824 @ col %ld? (next alternative)\n", _x);
        PACC_TRACE fprintf(stderr, "seq 823 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 823;
        _status = parsed;
        /* bind: w */
        PACC_TRACE fprintf(stderr, "bind 806 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind w @ rule 885, col %ld\n", _x);
        _pacc_save_core(885, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 805;
        _st = 885;
        /* call Word */
        goto top;
        case 805: /* return from Word */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 826);
        /* end bind: w */
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "expr 822 @ col %ld?\n", _x);
        assert(cur->expr_id == 0);
        cur->expr_id = 822;
        case 822:
        if (_evaling) {
          struct pacc_mid *_pacc_p;
          /* i is 0, type is ref_t */
          ref_t w;
          PACC_TRACE fprintf(stderr, "822: evaluating\n");
          _pacc_p = cur = _pacc_result(_pacc, _x, 826);
          _pos = 0;
          PACC_TRACE fprintf(stderr, "binding of w: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind w to r885 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 885);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 808;
            _pacc_ev_i = 0; goto eval_loop;
            case 808:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          w = cur->value.u4;
          PACC_TRACE fprintf(stderr, "bound w to r885 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          cur = _pacc_p;
          cur->value.u3=
#line 176 "parse.pacc"
            ( mk(nWord, ((struct Word *)w)->w, ((struct Word *)w)->m, ((struct Word *)w)->q) )
#line 7412 "parse.c"
          ;
          PACC_TRACE fprintf(stderr, "stash " TYPE_PRINTF " to (%ld, 826)\n", cur->value.u0, _x);
          goto _pacc_expr_done;
        }
        case 823:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 823 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        if (_status == no_parse) {
          PACC_TRACE fprintf(stderr, "restore column registers\n");
          _pacc_Pop(cur->ev_valid); _pacc_Pop(_x);
        }
        else {
          PACC_TRACE fprintf(stderr, "accept column registers\n");
          _pacc_Discard(cur->ev_valid); _pacc_Discard(_x);
        }
        case 824:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "alt 824 @ col %ld => %s\n", _x, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        cur->rule = (cur->rule & ~3) | _status;
        cur->remainder = _x;
        if (_pacc->err_col == _x_rule) {
          _pacc->err_valid = 0;
          _pacc_error(_pacc, ".comword", _x_rule);
        }
      }
      goto contin;
      case 843: /* Words */
      PACC_TRACE fprintf(stderr, "rule 843 (Words) col %ld\n", _x);
      _x_rule = _x;
      cur = _pacc_result(_pacc, _x, 843);
      if ((cur->rule & 3) == uncomputed) {
        PACC_TRACE fprintf(stderr, "alt 841 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 841;
        PACC_TRACE fprintf(stderr, "save column registers\n");
        _pacc_Push(_x); _pacc_Push(cur->ev_valid);
        PACC_TRACE fprintf(stderr, "seq 837 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 837;
        _status = parsed;
        /* bind: w */
        PACC_TRACE fprintf(stderr, "bind 828 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind w @ rule 885, col %ld\n", _x);
        _pacc_save_core(885, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 827;
        _st = 885;
        /* call Word */
        goto top;
        case 827: /* return from Word */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 843);
        /* end bind: w */
        if (_status == no_parse) {
          goto contin;
        }
        /* bind: ws */
        PACC_TRACE fprintf(stderr, "bind 830 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind ws @ rule 843, col %ld\n", _x);
        _pacc_save_core(843, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 829;
        _st = 843;
        /* call Words */
        goto top;
        case 829: /* return from Words */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 843);
        /* end bind: ws */
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "expr 836 @ col %ld?\n", _x);
        assert(cur->expr_id == 0);
        cur->expr_id = 836;
        case 836:
        if (_evaling) {
          struct pacc_mid *_pacc_p;
          /* i is 0, type is ref_t */
          ref_t w;
          /* i is 1, type is struct Node * */
          struct Node * ws;
          PACC_TRACE fprintf(stderr, "836: evaluating\n");
          _pacc_p = cur = _pacc_result(_pacc, _x, 843);
          _pos = 0;
          PACC_TRACE fprintf(stderr, "binding of w: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind w to r885 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 885);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 832;
            _pacc_ev_i = 0; goto eval_loop;
            case 832:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          w = cur->value.u4;
          PACC_TRACE fprintf(stderr, "bound w to r885 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          _pos = 1;
          PACC_TRACE fprintf(stderr, "binding of ws: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind ws to r843 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 843);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 831;
            _pacc_ev_i = 0; goto eval_loop;
            case 831:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          ws = cur->value.u3;
          PACC_TRACE fprintf(stderr, "bound ws to r843 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          cur = _pacc_p;
          cur->value.u3=
#line 192 "parse.pacc"
                        ( mk(nLappend, w, ws) )
#line 7537 "parse.c"
          ;
          PACC_TRACE fprintf(stderr, "stash " TYPE_PRINTF " to (%ld, 843)\n", cur->value.u0, _x);
          goto _pacc_expr_done;
        }
        case 837:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 837 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 841 @ col %ld => %s\n", _x, _status!=no_parse?"yes":"no");
        if (_status != no_parse) {
          PACC_TRACE fprintf(stderr, "accept column registers\n");
          _pacc_Discard(cur->ev_valid); _pacc_Discard(_x);
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "restore column registers\n");
        _pacc_Pop(cur->ev_valid); _pacc_Pop(_x);
        PACC_TRACE fprintf(stderr, "save column registers\n");
        _pacc_Push(_x); _pacc_Push(cur->ev_valid);
        PACC_TRACE fprintf(stderr, "col restored to %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 841 @ col %ld? (next alternative)\n", _x);
        PACC_TRACE fprintf(stderr, "seq 840 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 840;
        _status = parsed;
        PACC_TRACE fprintf(stderr, "expr 839 @ col %ld?\n", _x);
        assert(cur->expr_id == 0);
        cur->expr_id = 839;
        case 839:
        if (_evaling) {
          struct pacc_mid *_pacc_p;
          PACC_TRACE fprintf(stderr, "839: evaluating\n");
          _pacc_p = cur = _pacc_result(_pacc, _x, 843);
          cur = _pacc_p;
          cur->value.u3=
#line 193 "parse.pacc"
      (0)
#line 7574 "parse.c"
          ;
          PACC_TRACE fprintf(stderr, "stash " TYPE_PRINTF " to (%ld, 843)\n", cur->value.u0, _x);
          goto _pacc_expr_done;
        }
        case 840:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 840 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        if (_status == no_parse) {
          PACC_TRACE fprintf(stderr, "restore column registers\n");
          _pacc_Pop(cur->ev_valid); _pacc_Pop(_x);
        }
        else {
          PACC_TRACE fprintf(stderr, "accept column registers\n");
          _pacc_Discard(cur->ev_valid); _pacc_Discard(_x);
        }
        case 841:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "alt 841 @ col %ld => %s\n", _x, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        cur->rule = (cur->rule & ~3) | _status;
        cur->remainder = _x;
        if (_pacc->err_col == _x_rule) {
          _pacc->err_valid = 0;
          _pacc_error(_pacc, ".Words", _x_rule);
        }
      }
      goto contin;
      case 875: /* nlwords */
      PACC_TRACE fprintf(stderr, "rule 875 (nlwords) col %ld\n", _x);
      _x_rule = _x;
      cur = _pacc_result(_pacc, _x, 875);
      if ((cur->rule & 3) == uncomputed) {
        PACC_TRACE fprintf(stderr, "alt 873 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 873;
        PACC_TRACE fprintf(stderr, "save column registers\n");
        _pacc_Push(_x); _pacc_Push(cur->ev_valid);
        PACC_TRACE fprintf(stderr, "seq 847 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 847;
        _status = parsed;
        PACC_TRACE fprintf(stderr, "expr 846 @ col %ld?\n", _x);
        assert(cur->expr_id == 0);
        cur->expr_id = 846;
        case 846:
        if (_evaling) {
          struct pacc_mid *_pacc_p;
          PACC_TRACE fprintf(stderr, "846: evaluating\n");
          _pacc_p = cur = _pacc_result(_pacc, _x, 875);
          cur = _pacc_p;
          cur->value.u3=
#line 195 "parse.pacc"
           ( NULL )
#line 7629 "parse.c"
          ;
          PACC_TRACE fprintf(stderr, "stash " TYPE_PRINTF " to (%ld, 875)\n", cur->value.u0, _x);
          goto _pacc_expr_done;
        }
        case 847:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 847 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 873 @ col %ld => %s\n", _x, _status!=no_parse?"yes":"no");
        if (_status != no_parse) {
          PACC_TRACE fprintf(stderr, "accept column registers\n");
          _pacc_Discard(cur->ev_valid); _pacc_Discard(_x);
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "restore column registers\n");
        _pacc_Pop(cur->ev_valid); _pacc_Pop(_x);
        PACC_TRACE fprintf(stderr, "save column registers\n");
        _pacc_Push(_x); _pacc_Push(cur->ev_valid);
        PACC_TRACE fprintf(stderr, "col restored to %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 873 @ col %ld? (next alternative)\n", _x);
        PACC_TRACE fprintf(stderr, "seq 855 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 855;
        _status = parsed;
        /* bind: ws */
        PACC_TRACE fprintf(stderr, "bind 849 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind ws @ rule 843, col %ld\n", _x);
        _pacc_save_core(843, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 848;
        _st = 843;
        /* call Words */
        goto top;
        case 848: /* return from Words */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 875);
        /* end bind: ws */
        if (_status == no_parse) {
          goto contin;
        }
        _pacc_save_core(986, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 851;
        _st = 986;
        /* call nlwords:*:0 */
        goto top;
        case 851: /* return from nlwords:*:0 */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 875);
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "expr 854 @ col %ld?\n", _x);
        assert(cur->expr_id == 0);
        cur->expr_id = 854;
        case 854:
        if (_evaling) {
          struct pacc_mid *_pacc_p;
          /* i is 0, type is struct Node * */
          struct Node * ws;
          PACC_TRACE fprintf(stderr, "854: evaluating\n");
          _pacc_p = cur = _pacc_result(_pacc, _x, 875);
          _pos = 0;
          PACC_TRACE fprintf(stderr, "binding of ws: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind ws to r843 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 843);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 852;
            _pacc_ev_i = 0; goto eval_loop;
            case 852:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          ws = cur->value.u3;
          PACC_TRACE fprintf(stderr, "bound ws to r843 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          cur = _pacc_p;
          cur->value.u3=
#line 196 "parse.pacc"
                   (ws)
#line 7717 "parse.c"
          ;
          PACC_TRACE fprintf(stderr, "stash " TYPE_PRINTF " to (%ld, 875)\n", cur->value.u0, _x);
          goto _pacc_expr_done;
        }
        case 855:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 855 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 873 @ col %ld => %s\n", _x, _status!=no_parse?"yes":"no");
        if (_status != no_parse) {
          PACC_TRACE fprintf(stderr, "accept column registers\n");
          _pacc_Discard(cur->ev_valid); _pacc_Discard(_x);
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "restore column registers\n");
        _pacc_Pop(cur->ev_valid); _pacc_Pop(_x);
        PACC_TRACE fprintf(stderr, "save column registers\n");
        _pacc_Push(_x); _pacc_Push(cur->ev_valid);
        PACC_TRACE fprintf(stderr, "col restored to %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 873 @ col %ld? (next alternative)\n", _x);
        PACC_TRACE fprintf(stderr, "seq 872 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 872;
        _status = parsed;
        /* bind: w */
        PACC_TRACE fprintf(stderr, "bind 857 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind w @ rule 695, col %ld\n", _x);
        _pacc_save_core(695, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 856;
        _st = 695;
        /* call word */
        goto top;
        case 856: /* return from word */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 875);
        /* end bind: w */
        if (_status == no_parse) {
          goto contin;
        }
        /* bind: ws */
        PACC_TRACE fprintf(stderr, "bind 859 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind ws @ rule 875, col %ld\n", _x);
        _pacc_save_core(875, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 858;
        _st = 875;
        /* call nlwords */
        goto top;
        case 858: /* return from nlwords */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 875);
        /* end bind: ws */
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "expr 871 @ col %ld?\n", _x);
        assert(cur->expr_id == 0);
        cur->expr_id = 871;
        case 871:
        if (_evaling) {
          struct pacc_mid *_pacc_p;
          /* i is 0, type is struct Node * */
          struct Node * w;
          /* i is 1, type is struct Node * */
          struct Node * ws;
          PACC_TRACE fprintf(stderr, "871: evaluating\n");
          _pacc_p = cur = _pacc_result(_pacc, _x, 875);
          _pos = 0;
          PACC_TRACE fprintf(stderr, "binding of w: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind w to r695 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 695);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 861;
            _pacc_ev_i = 0; goto eval_loop;
            case 861:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          w = cur->value.u3;
          PACC_TRACE fprintf(stderr, "bound w to r695 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          _pos = 1;
          PACC_TRACE fprintf(stderr, "binding of ws: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind ws to r875 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 875);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 860;
            _pacc_ev_i = 0; goto eval_loop;
            case 860:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          ws = cur->value.u3;
          PACC_TRACE fprintf(stderr, "bound ws to r875 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          cur = _pacc_p;
          cur->value.u3=
#line 197 "parse.pacc"
                      ( (w != NULL ? (ws != NULL ? mk(nLappend, w, ws) : w) : ws) )
#line 7824 "parse.c"
          ;
          PACC_TRACE fprintf(stderr, "stash " TYPE_PRINTF " to (%ld, 875)\n", cur->value.u0, _x);
          goto _pacc_expr_done;
        }
        case 872:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 872 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        if (_status == no_parse) {
          PACC_TRACE fprintf(stderr, "restore column registers\n");
          _pacc_Pop(cur->ev_valid); _pacc_Pop(_x);
        }
        else {
          PACC_TRACE fprintf(stderr, "accept column registers\n");
          _pacc_Discard(cur->ev_valid); _pacc_Discard(_x);
        }
        case 873:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "alt 873 @ col %ld => %s\n", _x, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        cur->rule = (cur->rule & ~3) | _status;
        cur->remainder = _x;
        if (_pacc->err_col == _x_rule) {
          _pacc->err_valid = 0;
          _pacc_error(_pacc, ".nlwords", _x_rule);
        }
      }
      goto contin;
      case 885: /* Word */
      PACC_TRACE fprintf(stderr, "rule 885 (Word) col %ld\n", _x);
      _x_rule = _x;
      cur = _pacc_result(_pacc, _x, 885);
      if ((cur->rule & 3) == uncomputed) {
        PACC_TRACE fprintf(stderr, "seq 883 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 883;
        _status = parsed;
        /* bind: w */
        PACC_TRACE fprintf(stderr, "bind 878 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "will bind w @ rule 959, col %ld\n", _x);
        _pacc_save_core(959, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 960;
        _st = 959;
        /* call Word:w:0 */
        goto top;
        case 960: /* return from Word:w:0 */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 885);
        /* end bind: w */
        if (_status == no_parse) {
          goto contin;
        }
        _pacc_save_core(348, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 879;
        _st = 348;
        /* call _ */
        goto top;
        case 879: /* return from _ */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 885);
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "expr 882 @ col %ld?\n", _x);
        assert(cur->expr_id == 0);
        cur->expr_id = 882;
        case 882:
        if (_evaling) {
          struct pacc_mid *_pacc_p;
          /* i is 0, type is ref_t */
          ref_t w;
          PACC_TRACE fprintf(stderr, "882: evaluating\n");
          _pacc_p = cur = _pacc_result(_pacc, _x, 885);
          _pos = 0;
          PACC_TRACE fprintf(stderr, "binding of w: pos %ld holds col %ld\n", _pos, _pacc_p->evlis[_pos].col);
          PACC_TRACE fprintf(stderr, "bind w to r959 @ c%ld\n", _pacc_p->evlis[_pos].col);
          cur = _pacc_result(_pacc, _pacc_p->evlis[_pos].col, 959);
          if ((cur->rule & 3) != evaluated) {
            _pacc_Push(_x); _pacc_Push(_cont);
            _cont = 880;
            _pacc_ev_i = 0; goto eval_loop;
            case 880:
            _pacc_Pop(_cont); _pacc_Pop(_x);
          }
          w = cur->value.u4;
          PACC_TRACE fprintf(stderr, "bound w to r959 @ c%ld ==> " TYPE_PRINTF "\n", _pacc_p->evlis[_pos].col, cur->value.u0);
          cur = _pacc_p;
          cur->value.u4=
#line 200 "parse.pacc"
                                  (w)
#line 7925 "parse.c"
          ;
          PACC_TRACE fprintf(stderr, "stash " TYPE_PRINTF " to (%ld, 885)\n", cur->value.u0, _x);
          goto _pacc_expr_done;
        }
        case 883:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 883 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        cur->rule = (cur->rule & ~3) | _status;
        cur->remainder = _x;
        if (_pacc->err_col == _x_rule) {
          _pacc->err_valid = 0;
          _pacc_error(_pacc, ".Word", _x_rule);
        }
      }
      goto contin;
      case 890: /* And */
      PACC_TRACE fprintf(stderr, "rule 890 (And) col %ld\n", _x);
      _x_rule = _x;
      cur = _pacc_result(_pacc, _x, 890);
      if ((cur->rule & 3) == uncomputed) {
        PACC_TRACE fprintf(stderr, "seq 888 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 888;
        _status = parsed;
        PACC_TRACE fprintf(stderr, "lit 886 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "lit 886 @ col %ld => ", _x);
        if (_x+1 <= _pacc->input_length && memcmp("&", _pacc->string + _x, 1) == 0) {
          _status = parsed;
          _x += 1;
        }
        else {
          _pacc_error(_pacc, ".\"&\"", _x);
          _status = no_parse;
        }
        PACC_TRACE fprintf(stderr, "lit 886 %ld => %s\n", _x, _status != no_parse ? "yes" : "no");
        if (_status == no_parse) {
          goto contin;
        }
        _pacc_save_core(348, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 887;
        _st = 348;
        /* call _ */
        goto top;
        case 887: /* return from _ */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 890);
        case 888:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 888 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        cur->rule = (cur->rule & ~3) | _status;
        cur->remainder = _x;
        if (_pacc->err_col == _x_rule) {
          _pacc->err_valid = 0;
          _pacc_error(_pacc, ".And", _x_rule);
        }
      }
      goto contin;
      case 895: /* Bang */
      PACC_TRACE fprintf(stderr, "rule 895 (Bang) col %ld\n", _x);
      _x_rule = _x;
      cur = _pacc_result(_pacc, _x, 895);
      if ((cur->rule & 3) == uncomputed) {
        PACC_TRACE fprintf(stderr, "seq 893 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 893;
        _status = parsed;
        PACC_TRACE fprintf(stderr, "lit 891 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "lit 891 @ col %ld => ", _x);
        if (_x+1 <= _pacc->input_length && memcmp("!", _pacc->string + _x, 1) == 0) {
          _status = parsed;
          _x += 1;
        }
        else {
          _pacc_error(_pacc, ".\"!\"", _x);
          _status = no_parse;
        }
        PACC_TRACE fprintf(stderr, "lit 891 %ld => %s\n", _x, _status != no_parse ? "yes" : "no");
        if (_status == no_parse) {
          goto contin;
        }
        _pacc_save_core(348, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 892;
        _st = 348;
        /* call _ */
        goto top;
        case 892: /* return from _ */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 895);
        case 893:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 893 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        cur->rule = (cur->rule & ~3) | _status;
        cur->remainder = _x;
        if (_pacc->err_col == _x_rule) {
          _pacc->err_valid = 0;
          _pacc_error(_pacc, ".Bang", _x_rule);
        }
      }
      goto contin;
      case 901: /* optCaret */
      PACC_TRACE fprintf(stderr, "rule 901 (optCaret) col %ld\n", _x);
      _x_rule = _x;
      cur = _pacc_result(_pacc, _x, 901);
      if ((cur->rule & 3) == uncomputed) {
        PACC_TRACE fprintf(stderr, "seq 899 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 899;
        _status = parsed;
        _pacc_save_core(994, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 897;
        _st = 994;
        /* call optCaret:*:0 */
        goto top;
        case 897: /* return from optCaret:*:0 */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 901);
        if (_status == no_parse) {
          goto contin;
        }
        _pacc_save_core(348, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 898;
        _st = 348;
        /* call _ */
        goto top;
        case 898: /* return from _ */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 901);
        case 899:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 899 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        cur->rule = (cur->rule & ~3) | _status;
        cur->remainder = _x;
        if (_pacc->err_col == _x_rule) {
          _pacc->err_valid = 0;
          _pacc_error(_pacc, ".optCaret", _x_rule);
        }
      }
      goto contin;
      case 906: /* optNl */
      PACC_TRACE fprintf(stderr, "rule 906 (optNl) col %ld\n", _x);
      _x_rule = _x;
      cur = _pacc_result(_pacc, _x, 906);
      if ((cur->rule & 3) == uncomputed) {
        PACC_TRACE fprintf(stderr, "seq 904 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 904;
        _status = parsed;
        _pacc_save_core(1003, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 903;
        _st = 1003;
        /* call optNl:*:0 */
        goto top;
        case 903: /* return from optNl:*:0 */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 906);
        case 904:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 904 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        cur->rule = (cur->rule & ~3) | _status;
        cur->remainder = _x;
        if (_pacc->err_col == _x_rule) {
          _pacc->err_valid = 0;
          _pacc_error(_pacc, ".optNl", _x_rule);
        }
      }
      goto contin;
      case 911: /* lParen */
      PACC_TRACE fprintf(stderr, "rule 911 (lParen) col %ld\n", _x);
      _x_rule = _x;
      cur = _pacc_result(_pacc, _x, 911);
      if ((cur->rule & 3) == uncomputed) {
        PACC_TRACE fprintf(stderr, "seq 909 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 909;
        _status = parsed;
        PACC_TRACE fprintf(stderr, "lit 907 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "lit 907 @ col %ld => ", _x);
        if (_x+1 <= _pacc->input_length && memcmp("(", _pacc->string + _x, 1) == 0) {
          _status = parsed;
          _x += 1;
        }
        else {
          _pacc_error(_pacc, ".\"(\"", _x);
          _status = no_parse;
        }
        PACC_TRACE fprintf(stderr, "lit 907 %ld => %s\n", _x, _status != no_parse ? "yes" : "no");
        if (_status == no_parse) {
          goto contin;
        }
        _pacc_save_core(348, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 908;
        _st = 348;
        /* call _ */
        goto top;
        case 908: /* return from _ */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 911);
        case 909:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 909 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        cur->rule = (cur->rule & ~3) | _status;
        cur->remainder = _x;
        if (_pacc->err_col == _x_rule) {
          _pacc->err_valid = 0;
          _pacc_error(_pacc, ".lParen", _x_rule);
        }
      }
      goto contin;
      case 916: /* Tilde */
      PACC_TRACE fprintf(stderr, "rule 916 (Tilde) col %ld\n", _x);
      _x_rule = _x;
      cur = _pacc_result(_pacc, _x, 916);
      if ((cur->rule & 3) == uncomputed) {
        PACC_TRACE fprintf(stderr, "seq 914 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 914;
        _status = parsed;
        PACC_TRACE fprintf(stderr, "lit 912 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "lit 912 @ col %ld => ", _x);
        if (_x+1 <= _pacc->input_length && memcmp("~", _pacc->string + _x, 1) == 0) {
          _status = parsed;
          _x += 1;
        }
        else {
          _pacc_error(_pacc, ".\"~\"", _x);
          _status = no_parse;
        }
        PACC_TRACE fprintf(stderr, "lit 912 %ld => %s\n", _x, _status != no_parse ? "yes" : "no");
        if (_status == no_parse) {
          goto contin;
        }
        _pacc_save_core(348, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 913;
        _st = 348;
        /* call _ */
        goto top;
        case 913: /* return from _ */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 916);
        case 914:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 914 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        cur->rule = (cur->rule & ~3) | _status;
        cur->remainder = _x;
        if (_pacc->err_col == _x_rule) {
          _pacc->err_valid = 0;
          _pacc_error(_pacc, ".Tilde", _x_rule);
        }
      }
      goto contin;
      case 959: /* Word:w:0 */
      PACC_TRACE fprintf(stderr, "rule 959 (Word:w:0) col %ld\n", _x);
      _x_rule = _x;
      cur = _pacc_result(_pacc, _x, 959);
      if ((cur->rule & 3) == uncomputed) {
        PACC_TRACE fprintf(stderr, "seq 957 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 957;
        _status = parsed;
        _pacc_save_core(1013, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 877;
        _st = 1013;
        /* call Word:w:0:*:0 */
        goto top;
        case 877: /* return from Word:w:0:*:0 */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 959);
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "expr 956 @ col %ld?\n", _x);
        assert(cur->expr_id == 0);
        cur->expr_id = 956;
        case 956:
        if (_evaling) {
          struct pacc_mid *_pacc_p;
          PACC_TRACE fprintf(stderr, "956: evaluating\n");
          _pacc_p = cur = _pacc_result(_pacc, _x, 959);
          cur = _pacc_p;
          cur->value.u4=
(ref())
#line 8254 "parse.c"
          ;
          PACC_TRACE fprintf(stderr, "stash " TYPE_PRINTF " to (%ld, 959)\n", cur->value.u0, _x);
          goto _pacc_expr_done;
        }
        case 957:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 957 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        cur->rule = (cur->rule & ~3) | _status;
        cur->remainder = _x;
        if (_pacc->err_col == _x_rule) {
          _pacc->err_valid = 0;
          _pacc_error(_pacc, ".Word:w:0", _x_rule);
        }
      }
      goto contin;
      case 954: /* Decimal:d:0 */
      PACC_TRACE fprintf(stderr, "rule 954 (Decimal:d:0) col %ld\n", _x);
      _x_rule = _x;
      cur = _pacc_result(_pacc, _x, 954);
      if ((cur->rule & 3) == uncomputed) {
        PACC_TRACE fprintf(stderr, "seq 952 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 952;
        _status = parsed;
        _pacc_save_core(1023, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 328;
        _st = 1023;
        /* call Decimal:d:0:*:0 */
        goto top;
        case 328: /* return from Decimal:d:0:*:0 */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 954);
        if (_status == no_parse) {
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "expr 951 @ col %ld?\n", _x);
        assert(cur->expr_id == 0);
        cur->expr_id = 951;
        case 951:
        if (_evaling) {
          struct pacc_mid *_pacc_p;
          PACC_TRACE fprintf(stderr, "951: evaluating\n");
          _pacc_p = cur = _pacc_result(_pacc, _x, 954);
          cur = _pacc_p;
          cur->value.u4=
(ref())
#line 8307 "parse.c"
          ;
          PACC_TRACE fprintf(stderr, "stash " TYPE_PRINTF " to (%ld, 954)\n", cur->value.u0, _x);
          goto _pacc_expr_done;
        }
        case 952:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 952 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        cur->rule = (cur->rule & ~3) | _status;
        cur->remainder = _x;
        if (_pacc->err_col == _x_rule) {
          _pacc->err_valid = 0;
          _pacc_error(_pacc, ".Decimal:d:0", _x_rule);
        }
      }
      goto contin;
      case 1023: /* Decimal:d:0:*:0 */
      PACC_TRACE fprintf(stderr, "rule 1023 (Decimal:d:0:*:0) col %ld\n", _x);
      _x_rule = _x;
      cur = _pacc_result(_pacc, _x, 1023);
      if ((cur->rule & 3) == uncomputed) {
        PACC_TRACE fprintf(stderr, "alt 1021 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 1021;
        PACC_TRACE fprintf(stderr, "save column registers\n");
        _pacc_Push(_x); _pacc_Push(cur->ev_valid);
        PACC_TRACE fprintf(stderr, "seq 1020 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 1020;
        _status = parsed;
        _pacc_save_core(1015, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 1019;
        _st = 1015;
        /* call Decimal:d:0:1:0 */
        goto top;
        case 1019: /* return from Decimal:d:0:1:0 */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 1023);
        if (_status == no_parse) {
          goto contin;
        }
        _pacc_save_core(1023, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 1018;
        _st = 1023;
        /* call Decimal:d:0:*:0 */
        goto top;
        case 1018: /* return from Decimal:d:0:*:0 */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 1023);
        case 1020:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 1020 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 1021 @ col %ld => %s\n", _x, _status!=no_parse?"yes":"no");
        if (_status != no_parse) {
          PACC_TRACE fprintf(stderr, "accept column registers\n");
          _pacc_Discard(cur->ev_valid); _pacc_Discard(_x);
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "restore column registers\n");
        _pacc_Pop(cur->ev_valid); _pacc_Pop(_x);
        PACC_TRACE fprintf(stderr, "save column registers\n");
        _pacc_Push(_x); _pacc_Push(cur->ev_valid);
        PACC_TRACE fprintf(stderr, "col restored to %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 1021 @ col %ld? (next alternative)\n", _x);
        PACC_TRACE fprintf(stderr, "seq 1017 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 1017;
        _status = parsed;
        _pacc_save_core(1015, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 1016;
        _st = 1015;
        /* call Decimal:d:0:1:0 */
        goto top;
        case 1016: /* return from Decimal:d:0:1:0 */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 1023);
        case 1017:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 1017 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        if (_status == no_parse) {
          PACC_TRACE fprintf(stderr, "restore column registers\n");
          _pacc_Pop(cur->ev_valid); _pacc_Pop(_x);
        }
        else {
          PACC_TRACE fprintf(stderr, "accept column registers\n");
          _pacc_Discard(cur->ev_valid); _pacc_Discard(_x);
        }
        case 1021:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "alt 1021 @ col %ld => %s\n", _x, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        cur->rule = (cur->rule & ~3) | _status;
        cur->remainder = _x;
        if (_pacc->err_col == _x_rule) {
          _pacc->err_valid = 0;
          _pacc_error(_pacc, ".Decimal:d:0:*:0", _x_rule);
        }
      }
      goto contin;
      case 1015: /* Decimal:d:0:1:0 */
      PACC_TRACE fprintf(stderr, "rule 1015 (Decimal:d:0:1:0) col %ld\n", _x);
      _x_rule = _x;
      cur = _pacc_result(_pacc, _x, 1015);
      if ((cur->rule & 3) == uncomputed) {
        PACC_TRACE fprintf(stderr, "cclass 327 @ col %ld?\n", _x);
        if (_x < _pacc->input_length) {
          _pacc_any_i = _pacc_utf8_char(_pacc->string+_x, _pacc->input_length - _x, &_pacc_utf_cp);
          if (!_pacc_any_i) pacc_panic("invalid UTF-8 input");
          if ((_pacc_utf_cp>=48&&_pacc_utf_cp<=57)) {
            _status = parsed;
            _x += _pacc_any_i;
          }
          else {
            _pacc_error(_pacc, ".[0-9]", _x);
            _status = no_parse;
          }
        }
        else {
          _pacc_error(_pacc, ".[0-9]", _x);
          _status = no_parse;
        }
        PACC_TRACE fprintf(stderr, "cclass 327 %ld => %s\n", _x, _status != no_parse ? "yes" : "no");
        cur->rule = (cur->rule & ~3) | _status;
        cur->remainder = _x;
        if (_pacc->err_col == _x_rule) {
          _pacc->err_valid = 0;
          _pacc_error(_pacc, ".Decimal:d:0:1:0", _x_rule);
        }
      }
      goto contin;
      case 1013: /* Word:w:0:*:0 */
      PACC_TRACE fprintf(stderr, "rule 1013 (Word:w:0:*:0) col %ld\n", _x);
      _x_rule = _x;
      cur = _pacc_result(_pacc, _x, 1013);
      if ((cur->rule & 3) == uncomputed) {
        PACC_TRACE fprintf(stderr, "alt 1011 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 1011;
        PACC_TRACE fprintf(stderr, "save column registers\n");
        _pacc_Push(_x); _pacc_Push(cur->ev_valid);
        PACC_TRACE fprintf(stderr, "seq 1010 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 1010;
        _status = parsed;
        _pacc_save_core(1005, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 1009;
        _st = 1005;
        /* call Word:w:0:1:0 */
        goto top;
        case 1009: /* return from Word:w:0:1:0 */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 1013);
        if (_status == no_parse) {
          goto contin;
        }
        _pacc_save_core(1013, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 1008;
        _st = 1013;
        /* call Word:w:0:*:0 */
        goto top;
        case 1008: /* return from Word:w:0:*:0 */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 1013);
        case 1010:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 1010 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 1011 @ col %ld => %s\n", _x, _status!=no_parse?"yes":"no");
        if (_status != no_parse) {
          PACC_TRACE fprintf(stderr, "accept column registers\n");
          _pacc_Discard(cur->ev_valid); _pacc_Discard(_x);
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "restore column registers\n");
        _pacc_Pop(cur->ev_valid); _pacc_Pop(_x);
        PACC_TRACE fprintf(stderr, "save column registers\n");
        _pacc_Push(_x); _pacc_Push(cur->ev_valid);
        PACC_TRACE fprintf(stderr, "col restored to %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 1011 @ col %ld? (next alternative)\n", _x);
        PACC_TRACE fprintf(stderr, "seq 1007 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 1007;
        _status = parsed;
        _pacc_save_core(1005, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 1006;
        _st = 1005;
        /* call Word:w:0:1:0 */
        goto top;
        case 1006: /* return from Word:w:0:1:0 */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 1013);
        case 1007:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 1007 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        if (_status == no_parse) {
          PACC_TRACE fprintf(stderr, "restore column registers\n");
          _pacc_Pop(cur->ev_valid); _pacc_Pop(_x);
        }
        else {
          PACC_TRACE fprintf(stderr, "accept column registers\n");
          _pacc_Discard(cur->ev_valid); _pacc_Discard(_x);
        }
        case 1011:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "alt 1011 @ col %ld => %s\n", _x, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        cur->rule = (cur->rule & ~3) | _status;
        cur->remainder = _x;
        if (_pacc->err_col == _x_rule) {
          _pacc->err_valid = 0;
          _pacc_error(_pacc, ".Word:w:0:*:0", _x_rule);
        }
      }
      goto contin;
      case 1005: /* Word:w:0:1:0 */
      PACC_TRACE fprintf(stderr, "rule 1005 (Word:w:0:1:0) col %ld\n", _x);
      _x_rule = _x;
      cur = _pacc_result(_pacc, _x, 1005);
      if ((cur->rule & 3) == uncomputed) {
        PACC_TRACE fprintf(stderr, "cclass 876 @ col %ld?\n", _x);
        if (_x < _pacc->input_length) {
          _pacc_any_i = _pacc_utf8_char(_pacc->string+_x, _pacc->input_length - _x, &_pacc_utf_cp);
          if (!_pacc_any_i) pacc_panic("invalid UTF-8 input");
          if ((_pacc_utf_cp>=65&&_pacc_utf_cp<=90) || (_pacc_utf_cp>=97&&_pacc_utf_cp<=122) || (_pacc_utf_cp>=48&&_pacc_utf_cp<=57)) {
            _status = parsed;
            _x += _pacc_any_i;
          }
          else {
            _pacc_error(_pacc, ".[A-Za-z0-9]", _x);
            _status = no_parse;
          }
        }
        else {
          _pacc_error(_pacc, ".[A-Za-z0-9]", _x);
          _status = no_parse;
        }
        PACC_TRACE fprintf(stderr, "cclass 876 %ld => %s\n", _x, _status != no_parse ? "yes" : "no");
        cur->rule = (cur->rule & ~3) | _status;
        cur->remainder = _x;
        if (_pacc->err_col == _x_rule) {
          _pacc->err_valid = 0;
          _pacc_error(_pacc, ".Word:w:0:1:0", _x_rule);
        }
      }
      goto contin;
      case 1003: /* optNl:*:0 */
      PACC_TRACE fprintf(stderr, "rule 1003 (optNl:*:0) col %ld\n", _x);
      _x_rule = _x;
      cur = _pacc_result(_pacc, _x, 1003);
      if ((cur->rule & 3) == uncomputed) {
        PACC_TRACE fprintf(stderr, "alt 1001 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 1001;
        PACC_TRACE fprintf(stderr, "save column registers\n");
        _pacc_Push(_x); _pacc_Push(cur->ev_valid);
        PACC_TRACE fprintf(stderr, "seq 1000 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 1000;
        _status = parsed;
        _pacc_save_core(996, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 999;
        _st = 996;
        /* call optNl:1:0 */
        goto top;
        case 999: /* return from optNl:1:0 */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 1003);
        if (_status == no_parse) {
          goto contin;
        }
        _pacc_save_core(1003, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 998;
        _st = 1003;
        /* call optNl:*:0 */
        goto top;
        case 998: /* return from optNl:*:0 */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 1003);
        case 1000:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 1000 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 1001 @ col %ld => %s\n", _x, _status!=no_parse?"yes":"no");
        if (_status != no_parse) {
          PACC_TRACE fprintf(stderr, "accept column registers\n");
          _pacc_Discard(cur->ev_valid); _pacc_Discard(_x);
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "restore column registers\n");
        _pacc_Pop(cur->ev_valid); _pacc_Pop(_x);
        PACC_TRACE fprintf(stderr, "save column registers\n");
        _pacc_Push(_x); _pacc_Push(cur->ev_valid);
        PACC_TRACE fprintf(stderr, "col restored to %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 1001 @ col %ld? (next alternative)\n", _x);
        PACC_TRACE fprintf(stderr, "seq 997 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 997;
        _status = parsed;
        case 997:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 997 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        if (_status == no_parse) {
          PACC_TRACE fprintf(stderr, "restore column registers\n");
          _pacc_Pop(cur->ev_valid); _pacc_Pop(_x);
        }
        else {
          PACC_TRACE fprintf(stderr, "accept column registers\n");
          _pacc_Discard(cur->ev_valid); _pacc_Discard(_x);
        }
        case 1001:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "alt 1001 @ col %ld => %s\n", _x, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        cur->rule = (cur->rule & ~3) | _status;
        cur->remainder = _x;
        if (_pacc->err_col == _x_rule) {
          _pacc->err_valid = 0;
          _pacc_error(_pacc, ".optNl:*:0", _x_rule);
        }
      }
      goto contin;
      case 996: /* optNl:1:0 */
      PACC_TRACE fprintf(stderr, "rule 996 (optNl:1:0) col %ld\n", _x);
      _x_rule = _x;
      cur = _pacc_result(_pacc, _x, 996);
      if ((cur->rule & 3) == uncomputed) {
        PACC_TRACE fprintf(stderr, "lit 902 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "lit 902 @ col %ld => ", _x);
        if (_x+1 <= _pacc->input_length && memcmp("\n", _pacc->string + _x, 1) == 0) {
          _status = parsed;
          _x += 1;
        }
        else {
          _pacc_error(_pacc, ".\"\n\"", _x);
          _status = no_parse;
        }
        PACC_TRACE fprintf(stderr, "lit 902 %ld => %s\n", _x, _status != no_parse ? "yes" : "no");
        cur->rule = (cur->rule & ~3) | _status;
        cur->remainder = _x;
        if (_pacc->err_col == _x_rule) {
          _pacc->err_valid = 0;
          _pacc_error(_pacc, ".optNl:1:0", _x_rule);
        }
      }
      goto contin;
      case 994: /* optCaret:*:0 */
      PACC_TRACE fprintf(stderr, "rule 994 (optCaret:*:0) col %ld\n", _x);
      _x_rule = _x;
      cur = _pacc_result(_pacc, _x, 994);
      if ((cur->rule & 3) == uncomputed) {
        PACC_TRACE fprintf(stderr, "alt 992 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 992;
        PACC_TRACE fprintf(stderr, "save column registers\n");
        _pacc_Push(_x); _pacc_Push(cur->ev_valid);
        PACC_TRACE fprintf(stderr, "seq 991 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 991;
        _status = parsed;
        _pacc_save_core(988, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 990;
        _st = 988;
        /* call optCaret:1:0 */
        goto top;
        case 990: /* return from optCaret:1:0 */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 994);
        case 991:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 991 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 992 @ col %ld => %s\n", _x, _status!=no_parse?"yes":"no");
        if (_status != no_parse) {
          PACC_TRACE fprintf(stderr, "accept column registers\n");
          _pacc_Discard(cur->ev_valid); _pacc_Discard(_x);
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "restore column registers\n");
        _pacc_Pop(cur->ev_valid); _pacc_Pop(_x);
        PACC_TRACE fprintf(stderr, "save column registers\n");
        _pacc_Push(_x); _pacc_Push(cur->ev_valid);
        PACC_TRACE fprintf(stderr, "col restored to %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 992 @ col %ld? (next alternative)\n", _x);
        PACC_TRACE fprintf(stderr, "seq 989 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 989;
        _status = parsed;
        case 989:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 989 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        if (_status == no_parse) {
          PACC_TRACE fprintf(stderr, "restore column registers\n");
          _pacc_Pop(cur->ev_valid); _pacc_Pop(_x);
        }
        else {
          PACC_TRACE fprintf(stderr, "accept column registers\n");
          _pacc_Discard(cur->ev_valid); _pacc_Discard(_x);
        }
        case 992:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "alt 992 @ col %ld => %s\n", _x, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        cur->rule = (cur->rule & ~3) | _status;
        cur->remainder = _x;
        if (_pacc->err_col == _x_rule) {
          _pacc->err_valid = 0;
          _pacc_error(_pacc, ".optCaret:*:0", _x_rule);
        }
      }
      goto contin;
      case 988: /* optCaret:1:0 */
      PACC_TRACE fprintf(stderr, "rule 988 (optCaret:1:0) col %ld\n", _x);
      _x_rule = _x;
      cur = _pacc_result(_pacc, _x, 988);
      if ((cur->rule & 3) == uncomputed) {
        PACC_TRACE fprintf(stderr, "lit 896 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "lit 896 @ col %ld => ", _x);
        if (_x+1 <= _pacc->input_length && memcmp("^", _pacc->string + _x, 1) == 0) {
          _status = parsed;
          _x += 1;
        }
        else {
          _pacc_error(_pacc, ".\"^\"", _x);
          _status = no_parse;
        }
        PACC_TRACE fprintf(stderr, "lit 896 %ld => %s\n", _x, _status != no_parse ? "yes" : "no");
        cur->rule = (cur->rule & ~3) | _status;
        cur->remainder = _x;
        if (_pacc->err_col == _x_rule) {
          _pacc->err_valid = 0;
          _pacc_error(_pacc, ".optCaret:1:0", _x_rule);
        }
      }
      goto contin;
      case 986: /* nlwords:*:0 */
      PACC_TRACE fprintf(stderr, "rule 986 (nlwords:*:0) col %ld\n", _x);
      _x_rule = _x;
      cur = _pacc_result(_pacc, _x, 986);
      if ((cur->rule & 3) == uncomputed) {
        PACC_TRACE fprintf(stderr, "alt 984 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 984;
        PACC_TRACE fprintf(stderr, "save column registers\n");
        _pacc_Push(_x); _pacc_Push(cur->ev_valid);
        PACC_TRACE fprintf(stderr, "seq 983 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 983;
        _status = parsed;
        _pacc_save_core(980, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 982;
        _st = 980;
        /* call nlwords:1:0 */
        goto top;
        case 982: /* return from nlwords:1:0 */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 986);
        case 983:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 983 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 984 @ col %ld => %s\n", _x, _status!=no_parse?"yes":"no");
        if (_status != no_parse) {
          PACC_TRACE fprintf(stderr, "accept column registers\n");
          _pacc_Discard(cur->ev_valid); _pacc_Discard(_x);
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "restore column registers\n");
        _pacc_Pop(cur->ev_valid); _pacc_Pop(_x);
        PACC_TRACE fprintf(stderr, "save column registers\n");
        _pacc_Push(_x); _pacc_Push(cur->ev_valid);
        PACC_TRACE fprintf(stderr, "col restored to %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 984 @ col %ld? (next alternative)\n", _x);
        PACC_TRACE fprintf(stderr, "seq 981 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 981;
        _status = parsed;
        case 981:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 981 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        if (_status == no_parse) {
          PACC_TRACE fprintf(stderr, "restore column registers\n");
          _pacc_Pop(cur->ev_valid); _pacc_Pop(_x);
        }
        else {
          PACC_TRACE fprintf(stderr, "accept column registers\n");
          _pacc_Discard(cur->ev_valid); _pacc_Discard(_x);
        }
        case 984:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "alt 984 @ col %ld => %s\n", _x, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        cur->rule = (cur->rule & ~3) | _status;
        cur->remainder = _x;
        if (_pacc->err_col == _x_rule) {
          _pacc->err_valid = 0;
          _pacc_error(_pacc, ".nlwords:*:0", _x_rule);
        }
      }
      goto contin;
      case 980: /* nlwords:1:0 */
      PACC_TRACE fprintf(stderr, "rule 980 (nlwords:1:0) col %ld\n", _x);
      _x_rule = _x;
      cur = _pacc_result(_pacc, _x, 980);
      if ((cur->rule & 3) == uncomputed) {
        PACC_TRACE fprintf(stderr, "lit 850 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "lit 850 @ col %ld => ", _x);
        if (_x+1 <= _pacc->input_length && memcmp("\n", _pacc->string + _x, 1) == 0) {
          _status = parsed;
          _x += 1;
        }
        else {
          _pacc_error(_pacc, ".\"\n\"", _x);
          _status = no_parse;
        }
        PACC_TRACE fprintf(stderr, "lit 850 %ld => %s\n", _x, _status != no_parse ? "yes" : "no");
        cur->rule = (cur->rule & ~3) | _status;
        cur->remainder = _x;
        if (_pacc->err_col == _x_rule) {
          _pacc->err_valid = 0;
          _pacc_error(_pacc, ".nlwords:1:0", _x_rule);
        }
      }
      goto contin;
      case 978: /* First:*:0 */
      PACC_TRACE fprintf(stderr, "rule 978 (First:*:0) col %ld\n", _x);
      _x_rule = _x;
      cur = _pacc_result(_pacc, _x, 978);
      if ((cur->rule & 3) == uncomputed) {
        PACC_TRACE fprintf(stderr, "alt 976 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 976;
        PACC_TRACE fprintf(stderr, "save column registers\n");
        _pacc_Push(_x); _pacc_Push(cur->ev_valid);
        PACC_TRACE fprintf(stderr, "seq 975 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 975;
        _status = parsed;
        _pacc_save_core(971, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 974;
        _st = 971;
        /* call First:1:0 */
        goto top;
        case 974: /* return from First:1:0 */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 978);
        if (_status == no_parse) {
          goto contin;
        }
        _pacc_save_core(978, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 973;
        _st = 978;
        /* call First:*:0 */
        goto top;
        case 973: /* return from First:*:0 */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 978);
        case 975:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 975 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 976 @ col %ld => %s\n", _x, _status!=no_parse?"yes":"no");
        if (_status != no_parse) {
          PACC_TRACE fprintf(stderr, "accept column registers\n");
          _pacc_Discard(cur->ev_valid); _pacc_Discard(_x);
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "restore column registers\n");
        _pacc_Pop(cur->ev_valid); _pacc_Pop(_x);
        PACC_TRACE fprintf(stderr, "save column registers\n");
        _pacc_Push(_x); _pacc_Push(cur->ev_valid);
        PACC_TRACE fprintf(stderr, "col restored to %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 976 @ col %ld? (next alternative)\n", _x);
        PACC_TRACE fprintf(stderr, "seq 972 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 972;
        _status = parsed;
        case 972:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 972 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        if (_status == no_parse) {
          PACC_TRACE fprintf(stderr, "restore column registers\n");
          _pacc_Pop(cur->ev_valid); _pacc_Pop(_x);
        }
        else {
          PACC_TRACE fprintf(stderr, "accept column registers\n");
          _pacc_Discard(cur->ev_valid); _pacc_Discard(_x);
        }
        case 976:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "alt 976 @ col %ld => %s\n", _x, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        cur->rule = (cur->rule & ~3) | _status;
        cur->remainder = _x;
        if (_pacc->err_col == _x_rule) {
          _pacc->err_valid = 0;
          _pacc_error(_pacc, ".First:*:0", _x_rule);
        }
      }
      goto contin;
      case 971: /* First:1:0 */
      PACC_TRACE fprintf(stderr, "rule 971 (First:1:0) col %ld\n", _x);
      _x_rule = _x;
      cur = _pacc_result(_pacc, _x, 971);
      if ((cur->rule & 3) == uncomputed) {
        PACC_TRACE fprintf(stderr, "seq 659 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 659;
        _status = parsed;
        PACC_TRACE fprintf(stderr, "lit 657 @ col %ld?\n", _x);
        PACC_TRACE fprintf(stderr, "lit 657 @ col %ld => ", _x);
        if (_x+1 <= _pacc->input_length && memcmp("^", _pacc->string + _x, 1) == 0) {
          _status = parsed;
          _x += 1;
        }
        else {
          _pacc_error(_pacc, ".\"^\"", _x);
          _status = no_parse;
        }
        PACC_TRACE fprintf(stderr, "lit 657 %ld => %s\n", _x, _status != no_parse ? "yes" : "no");
        if (_status == no_parse) {
          goto contin;
        }
        _pacc_save_core(674, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 658;
        _st = 674;
        /* call sword */
        goto top;
        case 658: /* return from sword */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 971);
        case 659:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 659 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        cur->rule = (cur->rule & ~3) | _status;
        cur->remainder = _x;
        if (_pacc->err_col == _x_rule) {
          _pacc->err_valid = 0;
          _pacc_error(_pacc, ".First:1:0", _x_rule);
        }
      }
      goto contin;
      case 969: /* _:*:0 */
      PACC_TRACE fprintf(stderr, "rule 969 (_:*:0) col %ld\n", _x);
      _x_rule = _x;
      cur = _pacc_result(_pacc, _x, 969);
      if ((cur->rule & 3) == uncomputed) {
        PACC_TRACE fprintf(stderr, "alt 967 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 967;
        PACC_TRACE fprintf(stderr, "save column registers\n");
        _pacc_Push(_x); _pacc_Push(cur->ev_valid);
        PACC_TRACE fprintf(stderr, "seq 966 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 966;
        _status = parsed;
        _pacc_save_core(962, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 965;
        _st = 962;
        /* call _:1:0 */
        goto top;
        case 965: /* return from _:1:0 */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 969);
        if (_status == no_parse) {
          goto contin;
        }
        _pacc_save_core(969, _x);
        _pacc_Push(_x_rule);
        _pacc_Push(_cont);
        _cont = 964;
        _st = 969;
        /* call _:*:0 */
        goto top;
        case 964: /* return from _:*:0 */
        _pacc_Pop(_cont);
        _status = cur->rule & 3;
        _x = cur->remainder;
        _pacc_Pop(_x_rule);
        cur = _pacc_result(_pacc, _x_rule, 969);
        case 966:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 966 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 967 @ col %ld => %s\n", _x, _status!=no_parse?"yes":"no");
        if (_status != no_parse) {
          PACC_TRACE fprintf(stderr, "accept column registers\n");
          _pacc_Discard(cur->ev_valid); _pacc_Discard(_x);
          goto contin;
        }
        PACC_TRACE fprintf(stderr, "restore column registers\n");
        _pacc_Pop(cur->ev_valid); _pacc_Pop(_x);
        PACC_TRACE fprintf(stderr, "save column registers\n");
        _pacc_Push(_x); _pacc_Push(cur->ev_valid);
        PACC_TRACE fprintf(stderr, "col restored to %ld\n", _x);
        PACC_TRACE fprintf(stderr, "alt 967 @ col %ld? (next alternative)\n", _x);
        PACC_TRACE fprintf(stderr, "seq 963 @ col %ld?\n", _x);
        _pacc_Push(_cont);
        _cont = 963;
        _status = parsed;
        case 963:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "seq 963 @ col %ld => %s\n", _x_rule, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        if (_status == no_parse) {
          PACC_TRACE fprintf(stderr, "restore column registers\n");
          _pacc_Pop(cur->ev_valid); _pacc_Pop(_x);
        }
        else {
          PACC_TRACE fprintf(stderr, "accept column registers\n");
          _pacc_Discard(cur->ev_valid); _pacc_Discard(_x);
        }
        case 967:
        _pacc_Pop(_cont);
        PACC_TRACE fprintf(stderr, "alt 967 @ col %ld => %s\n", _x, _status!=no_parse?"yes":"no");
        PACC_TRACE fprintf(stderr, "col is %ld\n", _x);
        cur->rule = (cur->rule & ~3) | _status;
        cur->remainder = _x;
        if (_pacc->err_col == _x_rule) {
          _pacc->err_valid = 0;
          _pacc_error(_pacc, "._:*:0", _x_rule);
        }
      }
      goto contin;
      case 962: /* _:1:0 */
      PACC_TRACE fprintf(stderr, "rule 962 (_:1:0) col %ld\n", _x);
      _x_rule = _x;
      cur = _pacc_result(_pacc, _x, 962);
      if ((cur->rule & 3) == uncomputed) {
        PACC_TRACE fprintf(stderr, "cclass 344 @ col %ld?\n", _x);
        if (_x < _pacc->input_length) {
          _pacc_any_i = _pacc_utf8_char(_pacc->string+_x, _pacc->input_length - _x, &_pacc_utf_cp);
          if (!_pacc_any_i) pacc_panic("invalid UTF-8 input");
          if (_pacc_utf_cp==32 || _pacc_utf_cp==9 || _pacc_utf_cp==10) {
            _status = parsed;
            _x += _pacc_any_i;
          }
          else {
            _pacc_error(_pacc, ".[ \t\n]", _x);
            _status = no_parse;
          }
        }
        else {
          _pacc_error(_pacc, ".[ \t\n]", _x);
          _status = no_parse;
        }
        PACC_TRACE fprintf(stderr, "cclass 344 %ld => %s\n", _x, _status != no_parse ? "yes" : "no");
        cur->rule = (cur->rule & ~3) | _status;
        cur->remainder = _x;
        if (_pacc->err_col == _x_rule) {
          _pacc->err_valid = 0;
          _pacc_error(_pacc, "._:1:0", _x_rule);
        }
      }
      goto contin;
      case -1: break;
    }

    _x = 0;
    cur = _pacc_result(_pacc, _x, start_rule_id);
    /* pacc grammars are anchored on the right */
    if ((cur->rule & 3) == parsed && cur->remainder != _pacc->input_length) {
	_pacc_error(_pacc, ".end-of-input", cur->remainder);
	cur->rule = (cur->rule & ~3) | no_parse;
    }
    if (!_evaling && (cur->rule & 3) == parsed) {
	unsigned char *stack_save;

	PACC_TRACE fprintf(stderr, "PARSED! Time to start eval...\n");
	_evaling = 1;
	_pacc_ev_i = 0;
    eval_loop:
	PACC_TRACE fprintf(stderr, "eval loop with _pacc_ev_i == %ld\n", _pacc_ev_i);
	stack_save = _pacc->sp;
    eval1:
	while (_pacc_ev_i < cur->ev_valid) {
	    int col, rule;
	    rule = cur->evlis[_pacc_ev_i].call_id;
	    col = cur->evlis[_pacc_ev_i].col;
	    ++_pacc_ev_i;
	    PACC_TRACE fprintf(stderr, "eval loop: r%d @ c%d\n", rule, col);
	    _pacc_Push(cur);
	    _pacc_Push(_pacc_ev_i);
	    cur = _pacc_result(_pacc, col, rule);
	    _pacc_ev_i = 0;
	}
	if ((cur->rule & 3) != evaluated && cur->expr_id) {
	    _x = cur->col;
	    _st = cur->expr_id;
	    goto top;
	}
    _pacc_expr_done:
	cur->rule = (cur->rule & ~3) | evaluated;
	if (_pacc->sp != stack_save) {
	    _pacc_Pop(_pacc_ev_i);
	    _pacc_Pop(cur);
	    goto eval1;
	}
	PACC_TRACE fprintf(stderr, "eval finished\n");
	goto contin;
    }

    PACC_TRACE {
	unsigned char min;
	unsigned int i;
	unsigned long a, v;

	a = v = 0;
	min = _pacc->m_chain_max;
	for (i = 0; i < _pacc->m_bkt_cnt; ++i) {
	    unsigned char valid = _pacc->m_valid[i * 2];
	    unsigned char alloc = _pacc->m_valid[i * 2 + 1];
	    fprintf(stderr, "%d/%d ", valid, alloc);
	    v += valid; a += alloc;
	    if (alloc < min)
		min = alloc;
	}
	fprintf(stderr, "\n");
	fprintf(stderr, "used %u buckets\n", _pacc->m_bkt_cnt);
	fprintf(stderr, "chain length from %d to %d\n", min, _pacc->m_chain_max);
	fprintf(stderr, "total used/allocated: %ld/%ld\n", v, a);
    }
    if ((cur->rule & 3) == evaluated) {
	PACC_TRACE fprintf(stderr, "parsed with value " TYPE_PRINTF "\n", cur->value.u0); /* XXX u0 */
	_pacc->value = cur->value.u0;
    } else if ((cur->rule & 3) == parsed) {
	PACC_TRACE fprintf(stderr, "parsed with void value\n");
    } else PACC_TRACE fprintf(stderr, "not parsed\n");
    return (cur->rule & 3) == evaluated;
}

PACC_TYPE PACC_SYM(result)(struct pacc_parser *p) {
    return p->value;
}

int PACC_SYM(wrap)(const char *name, char *addr, size_t l, PACC_TYPE *result) {
    int parsed;
    struct pacc_parser *p;

    p = PACC_SYM(new)();

    PACC_SYM(input)(p, addr, l);
    parsed = PACC_SYM(parse)(p);
    if (parsed) *result = PACC_SYM(result)(p);
    else {
	char *e = PACC_SYM(error)(p);
	fprintf(stderr, "%s:%s\n", name, e);
	free(e);
    }

    PACC_SYM(destroy)(p);

    return parsed;
}
