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
%token And Or Where TXCL TQ TSuspend TAbort TWhile
%token TLbrack TRbrack TColon TPresent TEof TLShift TRShift TElse TExit TEmit
%token TMain TIn TOut TOtherwise TPar TFor TSignal TChannel TPause
%token TInt8 TInt16 TInt32 TInt64 TInt8s TInt16s TInt32s TInt64s TFloat8 TFloat32 TFloat64 TFloat16
%token TExtern TSplit TAT

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
    | stmtlist TSEMICOLON stmt {$3::$1}
    | stmt {[$1]}
;

stmt:
    | TIn TSignal symbol {Systemj.Signal(Some Systemj.Input, $3, ln())}
    | TOut TSignal symbol {Systemj.Signal(Some Systemj.Output, $3, ln())}
    | TSignal symbol {Systemj.Signal(None, $2, ln())}
    | TIn TChannel symbol {Systemj.Channel(Systemj.Input, $3, ln())}
    | TOut TChannel symbol {Systemj.Channel(Systemj.Output, $3, ln())}
    | TOB stmtlist TCB {Systemj.Block ($2, ln())}
    | present {$1}
    | abort {$1}
    | suspend {$1}
    | TExit TOP symbol TCP {Systemj.Exit($3,ln())}
    | TEmit symbol {Systemj.Emit($2,ln())}
    | TPause {Systemj.Pause(ln())}
    | TSplit TOP stmtlist TCP {Systemj.Spar($3,ln())}
    | send {$1}
    | receive {$1}
;

send:
    | symbol TXCL {Systemj.Send($1,ln())}
;

receive:
    | symbol TQ  {Systemj.Receive($1,ln())}
;

suspend:
    | TSuspend TOP expr TCP stmt {Systemj.Suspend($3,$5,ln())}
;
abort:
    | TAbort TOP expr TCP stmt {Systemj.Abort($3,$5,ln())}
;

present:
    | TPresent TOP expr TCP stmt {Systemj.Present($3,$5,None,ln())}
    | TPresent TOP expr TCP stmt TElse stmt {Systemj.Present($3,$5,Some $7,ln())}
;

twhile:
    | TWhile TOP expr TCP stmt 

expr:
    | symbol {Systemj.Esymbol($1,ln())}
    | expr Or expr {Systemj.Or($1,$3,ln())}
    | expr And expr {Systemj.And($1,$3,ln())}
    | TOP expr TCP {Systemj.Brackets($2,ln())}
;

symbol:
    | TSymbol {Systemj.Symbol ($1, ln())} /*e.g.: t*/
;
%%
(* This is the trailer *)
