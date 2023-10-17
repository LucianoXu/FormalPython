# REM

This tool helps implement formal proofs in Python language, it adopts a methodology to represent proof terms in the formal proof system with class objects in Python, and it applies the type check in Python to make sure that the proof system is correctly utilized. In other words, it is an idea from Howard-Curry correspondence which transforms formal proof systems into Python executable codes, with correctness guaranteed. Using this mechanism, I implemented the COC logic system as an exmaple.

Principle of implementation:
- The global environment will always remain well-formed.
- Typed expressions are represented by `Expr` classes.
- The proof of typing is preserved as the `_T` member for that expression.
- The definitional equality of CIC is represented by the `__eq__` relation for `Expr` classes.

It is better to consider Dirac notations as the new sorts of CIC, because they follow different calculation rules, and in this way we can embed the operations of Dirac notations into the CIC system directly.


The file `metadef.py` provides the tools for construting the meta system. It includes:
- `RemTerm`: the class for all meta terms. It provides the following methods:
  - `Rem_type_check`, `Rem_consistency_check` and `Rem_other_check`: the standard checking method for the calculus, which provides standard formatted error report.
- `Rem_term` and `concrete_Rem_term`: the decorator to register the subclass of `RemTerm` and automatically generates the meta term information. `concrete_Rem_term` corresponds to concrete proof terms that can be actually constructed in the meta system.
- `Rem_system_check`: a method to check the validity of the current meta system and generates the document `meta_rule.txt`. This should be executed at the end of a meta system definition (typically at the end of the `__init__.py` file of the package.)