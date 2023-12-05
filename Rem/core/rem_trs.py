'''
The builtin term rewriting system in Rem.
'''

from __future__ import annotations

from typing import Union

from .rem import *

from .rem_module import *

'''
The type for a side condition.
- Parameters: reduction rule, matched term, unifier, module environment (can be empty)
- return : 
    - RemSubst : accept with new unifier.
    - None : reject.
'''
SideCond = Callable[["RemRedRule", RemTerm, RemSubst, Union[RemVTerm, None]], Union[RemSubst, None]]


class RemRedRule:
    def __init__(self, lhs : RemTerm, rhs : RemTerm, side_cond : SideCond | None = None, side_cond_doc : str = "<side cond>"):
        REM_type_check(lhs, RemTerm)
        REM_type_check(rhs, RemTerm)

        self.lhs = lhs
        self.rhs = rhs
        self.side_cond = side_cond

        if self.side_cond is None:
            self.side_cond_doc = ""
        else:
            self.side_cond_doc = side_cond_doc

    def __str__(self) -> str:
        return f"{self.side_cond_doc} ⊢ {self.lhs} → {self.rhs}"

    def rewrite(self, term : RemTerm, module : RemVTerm | None = None) -> RemTerm | None:
        '''
        Match and rewrite the term.
        Return the result of rewriting. Return None if not matched.
        '''
        matcher = RemMatching.single_match(self.lhs, term)
        if matcher is None:
            return None
        
        if self.side_cond is None:
            return matcher(self.rhs)
        
        # Check side conditions.
        else:
            new_matcher = self.side_cond(self, term, matcher, module)
            if new_matcher is None:
                return None
            else:
                return new_matcher(self.rhs)

class RemTRS:
    '''
    A term rewriting system

    Note: no renaming is considered here, so the variables in rewriting rules should be always unique, for example "?x".
    '''
    def __init__(self, rules : List[RemRedRule], module_sort : ModuleSort|None = None):
        '''
        Create a term rewriting system
        '''
        REM_type_check(rules, list)
        for rule in rules:
            REM_type_check(rule, RemRedRule)

        REM_type_check(module_sort, (ModuleSort, type(None)))

        self.rules = rules.copy()
        self.module_sort = module_sort


    def rewrite(self, term : RemTerm, module : RemVTerm | None = None) -> RemTerm | None:

        # Check the module environment
        if self.module_sort is not None:
            if module is None:
                raise REM_CONSTRUCTION_Error(f"The module environment for rewriting is not provided.")
            
            if not module.well_typed(self.module_sort):
                raise REM_Sort_Error(module, self.module_sort)
            
        # invocate the verification-free algorithm
        return self.__rewrite_iter(term, module)
    
    def rewrites(self, term : RemTerm, module : RemVTerm | None = None) -> RemTerm:

        # Check the module environment
        if self.module_sort is not None:
            if module is None:
                raise REM_CONSTRUCTION_Error(f"The module environment for rewriting is not provided.")
            
            if not module.well_typed(self.module_sort):
                raise REM_Sort_Error(module, self.module_sort)
            
        # invocate the verification-free algorithm
        
        new_term = term
        while new_term is not None:
            term = new_term
            new_term = self.__rewrite_iter(term, module)
        
        return term
    

    def __rewrite_iter(self, term : RemTerm, module : RemVTerm | None) -> RemTerm | None:
        '''
        Try to rewrite the term once.
        '''

        if isinstance(term, RemVar):
            for rule in self.rules:
                new_term = rule.rewrite(term, module)
                if new_term is not None:
                    return new_term
                
            return None
        
        elif isinstance(term, RemCons):
            # check the parameters
            for i in range(term.fun.arity):
                new_term = self.rewrite(term[i], module)
                if new_term is not None:
                    return term.replace(i, new_term)
                
            # check the function itself
            for rule in self.rules:
                new_term = rule.rewrite(term, module)
                if new_term is not None:
                    return new_term
            
            return None

        else:
            raise Exception()
        
