all: asg
	@echo "compiled"

SExp:
	scalac SExp.scala

Exp:
	scalac Exp.scala

asg:  SExp Exp
	scalac asg.scala

run:
	@scala asg




