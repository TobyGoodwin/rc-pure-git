#define PACC_NAME pacc
    
#define PACC_ASSERT 1
#define PACC_CAN_TRACE 1
    

/* note that this actually needs to appear before any system header
   files are included; byacc likes to throw in <stdlib.h> first. */
#include "rc.h"

static Node *star, *nolist;
Node *parsetree;	/* not using yylval because bison declares it as an auto */


#include <sys/types.h>
struct pacc_parser;
extern int pacc_trace;
extern struct pacc_parser *pacc_new(void);
extern void pacc_input(struct pacc_parser *, char *, size_t l);
extern void pacc_destroy(struct pacc_parser *);
extern int pacc_parse(struct pacc_parser *);
extern Node * pacc_result(struct pacc_parser *);
extern char *pacc_error(struct pacc_parser *);
extern char *pacc_pos(struct pacc_parser *, const char *);
extern int pacc_wrap(const char *, char *, size_t, Node * *result);
