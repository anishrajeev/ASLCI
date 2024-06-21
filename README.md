**(A)nother (S)imple (L)ambda (C)alculus (I)nterpreter**<br />
Run<br />
```dune build```<br />
then <br />
```dune exec ASLCI <filename>.lc```<br />
"\" is the lambda symbol<br />
NAT, BOOL, are base types and -> is the only type constructor for now (i.e. NAT -> BOOL is a function from NAT to BOOL)<br />
A function has to give a type to the argument (i.e. "\x:NAT->BOOL. x")<br />
Some examples are included<br />
If something is not parsing, throw more parantheses at it :)<br />
STLC is normalizing so it is not turing complete yet(Can't do recursion etc) <br />
The addition of recursive types(plan is equirecursive) will fix this! <br />
