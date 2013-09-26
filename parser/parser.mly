%{
(* This is the header *)
 (* let _ = Parsing.set_trace true in () *)
 let counter = ref 0
 let line_nums = Hashtbl.create (1000) 
 let parse_error s = 
   let mypos = Parsing.symbol_start_pos() in
   print_string (s ^ " (line number: ");
   print_int mypos.Lexing.pos_lnum;
   print_string (", column number: " ^ (string_of_int (mypos.Lexing.pos_cnum - mypos.Lexing.pos_bol)));
   print_endline ")";
   flush stdout
 let ln () = 
   let mypos = Parsing.symbol_start_pos() in 
   let cnum = (mypos.Lexing.pos_cnum) - (mypos.Lexing.pos_bol) in
   (mypos.Lexing.pos_lnum,cnum)
%}

/* These are the declarations */

/* The tokens */
/* Constant constructors */
%token TPlus TMinus TTimes TDiv TPow TOP TSEMICOLON TCP TEqual TOB TCB TComma TLess TLessEqual TGreater TGreaterEqual TEqualEqual TMod TASYNC
%token And Or Where TXCL TQ TSuspend TAbort TWhile TTrue TFalse TWhile TTrap
%token TLbrack TRbrack TColon TPresent TEof TLShift TRShift TElse TExit TEmit
%token TMain TIn TOut TOtherwise TPar TFor TSignal TChannel TPause TColon
%token TInt8 TInt16 TInt32 TInt64 TInt8s TInt16s TInt32s TInt64s TFloat8 TFloat32 TFloat64 TFloat16
%token TAwait Timm TExtern TSplit TAT TSend TReceive

/* Constructors with an argument */
%token <string> TInt
%token <string> TFloat
%token <string> TEscapedCode
%token <string> TSymbol

/* operator associative rules */
%left TRShift TLShift
%left TPlus TMinus
%left TTimes TDiv TMod
%left TPow
%left TOP TCP
%left And Or
%left TXCL
%nonassoc TUminus /* useful for difference between -2 and 1 - 2*/

/* The start of the parsing function */
%start ast
%type <Systemj.ast> ast /* Test if this is correct */

%%
/* These are the parsing rules */

ast:
    | topstmtlist TEof {Systemj.Apar($1,ln())}
;

topstmtlist:
    | topstmtlist TASYNC stmt {$3::$1}
    | stmt {[$1]}
;

stmtlist:
    | stmtlist stmt {$2::$1}
    | stmt {[$1]}
;

stmt:
    | TIn TSignal symbol TSEMICOLON {Systemj.Signal(Some Systemj.Input, $3, ln())}
    | TOut TSignal symbol TSEMICOLON {Systemj.Signal(Some Systemj.Output, $3, ln())}
    | TSignal symbol TSEMICOLON {Systemj.Signal(None, $2, ln())}
    | TIn TChannel symbol TSEMICOLON {Systemj.Channel(Systemj.Input, $3, ln())}
    | TOut TChannel symbol TSEMICOLON {Systemj.Channel(Systemj.Output, $3, ln())}
    | TOB TCB {Systemj.Noop}
    | TSEMICOLON {Systemj.Noop}
    | TOB stmtlist TCB {Systemj.Block ($2, ln())}
    | par {$1}
    | present {$1}
    | abort {$1}
    | await TSEMICOLON {$1}
    | suspend {$1}
    /*| TExit TOP symbol TCP TSEMICOLON {Systemj.Exit($3,ln())}*/
    | TEmit symbol TSEMICOLON {Systemj.Emit($2,None,ln())}
    | TPause TSEMICOLON {Systemj.Pause(None,ln())}
    | symbol TColon TPause TSEMICOLON {Systemj.Pause(Some (match $1 with Systemj.Symbol (x,_) -> x),ln())}
    | send TSEMICOLON {$1}
    | receive TSEMICOLON {$1}
    | twhile {$1}
    /*| trap {$1}*/
;

par:
    | stmt Or stmt {Systemj.Spar([$3;$1],ln())}
;

await:
    | TAwait TOP expr TCP {Systemj.Abort($3,Systemj.While(Systemj.True,Systemj.Pause(None,ln()),ln()),ln()) }
;

send:
    | symbol TXCL {Systemj.Send($1,ln())}
;

receive:
    | symbol TQ  {Systemj.Receive($1,ln())}
;

/*trap:
    | TTrap TOP symbol TCP stmt {Systemj.Trap($3,$5,ln())}
;*/

suspend:
    /*| TSuspend TOP Timm expr TCP stmt {Systemj.Noop}*/
    | TSuspend TOP expr TCP stmt {Systemj.Suspend($3,$5,ln())}
;
abort:
    | TAbort TOP Timm expr TCP stmt { Systemj.Present($4,Systemj.Noop,Some (Systemj.Abort($4,$6,ln())),ln())}
    | TAbort TOP expr TCP stmt {Systemj.Abort($3,$5,ln())}
;

present:
    | TPresent TOP expr TCP stmt {Systemj.Present($3,$5,None,ln())}
    | TPresent TOP expr TCP stmt TElse stmt {Systemj.Present($3,$5,Some $7,ln())}
;

twhile:
    | TWhile TOP bool_expr TCP stmt {Systemj.While($3,$5,ln())}
;

expr:
    | symbol {Systemj.Esymbol($1,ln())}
    | TXCL expr {Systemj.Not($2,ln())}
    | expr Or expr {Systemj.Or($1,$3,ln())}
    | expr And expr {Systemj.And($1,$3,ln())}
    | TOP expr TCP {Systemj.Brackets($2,ln())}
;

bool_expr:
    | TTrue {Systemj.True}
    | TFalse {Systemj.False}
;

symbol:
    | TSymbol {Systemj.Symbol ($1, ln())} /*e.g.: t*/
;

%%
(* This is the trailer *)
