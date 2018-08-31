# Argle

Argument parsing library for rust.
Many approaches to argument parsing decouple:
 - specifying what the arguments are, including their notional type,
   and validating that arguments are present
 - parsing arguments into a variable of said type, and validating
   that the provided value can be parsed

The goal of this library is to unify these two steps.
