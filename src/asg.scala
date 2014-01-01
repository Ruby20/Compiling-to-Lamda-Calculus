/**
  * u0868464
  * CS6475
  */

import java.io._
import SExp._
import Exp._


object asg { 
  def VOID = " (λ (void) void)"
  //Booleans defn :
  def TRUE = " (λ (t) (λ (f) (t " + VOID+ ")))"
  def FALSE = " (λ (t) (λ (f) (f " + VOID+ ")))"
  def ERROR = " (λ (_) ((λ (f) (f f)) (λ (f) (f f))))"
   
// Numerics in Lambda Calculus(Church encodings):
  def ZERO = "(λ (n)((n (λ (_)" + FALSE+"))" + TRUE + "))"
  def SUM = "(λ (n) (λ (m) (λ (f) (λ (z) ((m f) ((n f) z))))))"
  def MUL = " (λ (n)(λ (m)(λ (f)(λ (z)((m (n f)) z)))))"
  def PRED = " (λ (n) (λ (f) (λ (z) (((n (λ (g) (λ (h) (h (g f))))) (λ (u) z)) (λ (u) u)))))" 
  def SUB = "(λ (n) (λ (m)((m " + PRED + ") n)))"
  
 
 
//lists
  def NIL = "(λ (on-cons)(λ (on-nil)(on-nil " + VOID + ")))"
  def CONS  = "(λ (car) (λ (cdr)(λ (on-cons)(λ (on-nil)((on-cons car) cdr)))))"   
  def CAR = "(λ (list)((list (λ (car)(λ (cdr) car)))"+ ERROR+"))"
  def CDR = "(λ (list)((list (λ (car)(λ (cdr) cdr)))" +ERROR+ "))"
  def PAIR = "(λ (list) ((list (λ (_) (λ (_) " + TRUE+ "))) (λ (_) " + FALSE+")))"
  def NULL = " (λ (list) ((list (λ (_) (λ (_) " + FALSE + "))) (λ (_) " + TRUE+ ")))"
  def YCOMB = " ((λ (y) (λ (F) (F (λ (x) (((y y) F) x))))) (λ (y) (λ (F) (F (λ (x) (((y y) F) x))))))"
  def YExp = LambdaExp(List("y"), LambdaExp(List("F"), AppExp(RefExp("F"), List(LambdaExp(List("x"), AppExp(AppExp(AppExp(RefExp("y"), List(RefExp("y"))), List(RefExp("F"))), List(RefExp("x"))))))))
  def YvExp = AppExp(YExp, List(YExp))

   def applyFNTimes( x : Int, wrap : String):String = x match {
    case 0 => wrap;
    case _ => applyFNTimes(x-1, "(f "+wrap+")")
  }

  def churchNumeral(n : Int) : String = n match {
    case 0 => "(λ (f) (λ (z) z))" ;
    case _ => "(λ (f) (λ (z) " + applyFNTimes(n, "z")  + "))" 
  }

   def curry(p:List[String], body:String): String = p match {
      case head::tail => "(lambda (" + head +") " + curry(tail,body) + ")"; 
      case _=> body   
    } 
  
  // def YExp { 
   // }
    def compile(expIn : Exp): String = expIn match {
      case IntExp(x) => churchNumeral(x)
      case PlusExp(x, y) => "((" + SUM + compile(x)+")" + compile(y) + ")"
      case TimesExp(x,y) => "((" + MUL + compile(x) +")"+ compile(y) + ")"
      case SubExp(x,y) => "((" + SUB + compile(x) +")"+ compile(y) + ")"
      case ZeroPExp(x) => "("+ ZERO + compile(x) + ")" 
      case EqExp(x,y) => compile (AndExp((ZeroPExp(SubExp(x,y))),(ZeroPExp(SubExp(y,x))))) 
   
       case RefExp(x) => x.toString
       case LambdaExp(p,b) => curry(p,compile(b))
       case AppExp(f,args) => args.map(compile).foldLeft(compile(f))((a,b) =>"(" + a + " " + b + ")" )    
 
// Condiionals
      case BoolExp(b) =>{
        if (b == true) TRUE
        else FALSE
      }


       
      case IfExp(x,t,f) => "((" + compile(x) + "(λ (_) "+ compile(t) + ")) (λ (_) "+compile(f)+"))"
      case AndExp(x,y) =>"((" +  compile(x) + "(λ (_) " + compile(y) + ")) (λ (_) " + FALSE + "))"
      case OrExp(x,y) => "((" +  compile(x) + "(λ (_) " + TRUE + ")) (λ (_) " + compile(y) + "))"
      case NullExp() => NIL
      case ConsExp(x,y) => "((" + CONS + compile(x) + ")" + compile(y) +  ")"
      case CarExp(x) => "(" + CAR + compile(x) + ")"
      case CdrExp(x) => "(" + CDR + compile(x) + ")"
      case PairPExp(x) => "(" + PAIR + compile(x) + ")"
      case NullPExp(x) => "(" + NULL + compile(x) + ")" 
    // Binding and forms  
      case LetExp(v,exp,body) => compile(AppExp(LambdaExp(v,body),exp))
 // Letrec expr 
      case LetRecExp(f,lam,body) => compile(LetExp(List(f), List(AppExp(YvExp,List(LambdaExp(List(f),lam)))), body))       
      case _ => "case unknown" + expIn.toString() 
     
    }  
  
   def succ(n:Exp):String = "(+ n 1)"

    
def main(args: Array[String]) 
{
    //get the input
    val source = scala.io.Source.stdin;
    val sourcestring = source.getLines mkString "\n";
    val sexp = SExp.from(sourcestring);
    val exp = Exp.from(sexp);
    source.close();
    
    val output = compile(exp).toString();
    println(output);
  }

}

