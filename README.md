# REM

One serious problem of proof formalization in Python is to *guarantee the correctness*, therefore we propose REM (reliable encode mechanism). It is a methodology, as well as a tool, to practice Curry-Howard correspondence in Python language, and put formal proof systems into Python **as it is** - which is the philosophy of REM. 

It adopts a methodology to represent proof terms in the formal proof system with class objects in Python, and it applies the type check in Python to make sure that the proof system is correctly utilized. In other words, it is an transforms formal proof systems into Python executable codes, with correctness guaranteed. Using this mechanism, I implemented the COC logic system as an exmaple.


## REM details

The Rem tool consists of the following parts:

- `REMSystem`: this object manages the meta information of a formal system supported by `Rem`. A `REMSystem` instance should be created at the beginning of defining a formal system. It also include the lexer and parser component.
- `RemTerm`: the class for all meta terms. It provides the following methods:
  - `Rem_type_check`, `Rem_consistency_check` and `Rem_other_check`: the standard checking method for the calculus, which provides standard formatted error report.
  - `parsing_rule` : if this attribute is defined, it will be collected as a parsing rule for the construction of the parser. However, because of the _as it is_ methodology, it is not meant for complex parsings when factors other than the term structure is considered. The parsing rule here should be simple and direct.
- `Rem_term` and `concrete_Rem_term`: the decorator to register the subclass of `RemTerm` at a system instance of `REMSystem` and automatically generates the meta term information. `concrete_Rem_term` corresponds to concrete proof terms that can be actually constructed in the meta system.
- `Rem_system_build`: a method to check the validity of the current meta system and generates the document `meta_rule.txt`. This should be executed at the end of a meta system definition (typically at the end of the `__init__.py` file of the package.)

## Implementing formal systems

The package `Rem` provides the tools for construting the formal proof system in Python. The routine practice should be:


- Create a `REMSystem` instance, which manages the meta information of the formal system to be implemented.
- Defining subclasses of `RemTerm` or `RemProof`, which represents the formal terms in the system. Remember to register them at the `REMSystem` instance using the decorator `Rem_term` or `concrete_Rem_term`. Provide the information as described in `RemTerm`.
- If necessary, define the lexing/parsing rules with the interface provided by `REMSystem`.
- Confirm and check the implementation after all definitions, using the method `Rem_system_build`. It can also build the parser if corresponding rules have been defined. The invocation of `Rem_system_build` method is often conducted in the end of the `__init__.py` file of the package.

## Fusing two REM systems
REM supports the incremental implementation of formal systems. We can append `RemTerm` subclasses to `super_term` static attributes to create new subterm relation between different REM systems, and use `REMSystem.fuse_append` method to get the system after fusion. This fusiong includes proof terms (subclasses of `RemTerm`) and the lexing/parsing rules.

## lexing rule order
In PLY, the precedence of lexing rules works like this: for lexing rules provided by the regulare expression string, there are no guarantee of matching order, so it is not recommend for tokens with ambiguity. For lexing rules that provided by a function, it looks at the **source line** only, and tokens defined with less line number will be matched. This even works for token functions in different python files.


## Extendable Formal System!
from CoC to CiC to CiC + QHL ...


## other...

It is better to consider Dirac notations as the new sorts of CIC, because they follow different calculation rules, and in this way we can embed the operations of Dirac notations into the CIC system directly.
