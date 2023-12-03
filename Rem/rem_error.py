from __future__ import annotations

from typing import Type, Tuple

# the basic REM error
class REM_Error(Exception):
    pass

# the errors that happen when constructin the formal system
class REM_META_Error(REM_Error):
    pass

# the error during parser construction
class REM_Parser_Building_Error(REM_META_Error):
    pass

# the errors that happen during term construction with formal systems
class REM_CONSTRUCTION_Error(REM_Error):
    pass

class REM_Sort_Error(REM_CONSTRUCTION_Error):
    def __init__(self, obj, sort) -> None:
        self.obj = obj
        self.sort = sort

    def __str__(self) -> str:
        return f"\nThe term '{self.obj}' does not belong to sort '{self.sort}.'"

# the error of wrong syntax when parsing
class REM_Syntax_Error(REM_CONSTRUCTION_Error):
    pass

def REM_type_check(obj : object, target_type : Type | Tuple[Type, ...], error_type : Type[REM_Error] = REM_Error) -> None:

    if isinstance(target_type, tuple):
        for t in target_type:
            if isinstance(obj, t):
                return
        
        raise error_type("REM-type-check: The parameter expression '" + str(obj) + "' should be within type '" + str(target_type) + "', but is of type '"+ str(type(obj)) + "'.")

    elif not isinstance(obj, target_type):
        raise error_type("REM-type-check: The parameter expression '" + str(obj) + "' should be of type '" + str(target_type) + "', but is of type '"+ str(type(obj)) + "'.")

def REM_other_check(expr : bool, reason : str, error_type : Type[REM_Error] = REM_Error) -> None:
    if not expr:
        raise error_type("REM-other-check: Rem does not accept because: \n\n{}".format(reason))

def REM_warning(msg : str):
    print(f"Rem WARNING: {msg}")