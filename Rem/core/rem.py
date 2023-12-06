'''
R.E.M. Reliable Encode Mechanism
レム、ゼロから新世代の形式化ツール！

[formalization framework based on order-sorted universal algebra]
'''

from __future__ import annotations

from typing import Type, Tuple, Any, TypeVar, Sequence, List, Generic, Callable, Dict

from graphviz import Digraph

import inspect

import copy

from .rem_error import REM_META_Error, REM_CONSTRUCTION_Error, REM_type_check, REM_other_check, REM_warning, REM_Sort_Error

from .network import NetworkNode


# the type variable for different kinds of term constructions.
T_Cons = TypeVar("T_Cons", bound="RemCons")

class RemObject(Generic[T_Cons]):
    def vlayout(self, dot : Digraph, id : str, title : str):
        '''
        The layout function in Graphviz illustration
        '''
        pass

    def __hash__(self) -> int:
        return id(self)
    
    @property
    def graphvizID(self) -> str:
        return str(id(self))

class RemNamed(RemObject[T_Cons]):
    '''
    Named objects in Rem system.
    '''
    def __init__(self, name : str):

        if not isinstance(name, str):
            raise REM_META_Error(f"The object '{name}' is not a valid name for this function. It should be a string.")

        self.__name = name
        self.rule_doc : str | None = None

    @property
    def name(self) -> str:
        return self.__name
    
    def __str__(self) -> str:
        return self.__name

    def type_check(self, obj, T : Type, term : str) -> None:
        '''
        Checks whether object `obj` is of the type `T`.
        Raise a `REM_CONSTRUCTION_Error` when the type does not match.
        This is intended for the check for correct operations.
        '''
        if isinstance(T, Type):
            if isinstance(obj, T):
                return 
            
            msg = f"\n({self.name}): The parameter '{term}' should have Python type \n\n'{T}'\n\nbut Rem found the object \n\n'{obj}'\n\nactually has type \n\n'{type(obj)}'"
            
        else:
            raise REM_META_Error(f"({self.name}): Invalid parameter type/sort '{T}'.")
        
        if self.rule_doc is not None:
            msg += f"\n\n Rem reminds you of the rule.\n{self.rule_doc}"
        
        raise REM_CONSTRUCTION_Error(msg)
        

    def consistency_check(self, a, b, term : str) -> None:
        '''
        Checks whether `a == b` holds. They should both serve as the terms for `term` in the meta system.
        Raise a `REM_CONSTRUCTION_Error` when `a != b`.
        This is intended for the check of object consistency for correct operations.
        '''

        if a != b:
            msg = f"\n({self.name}): Rem found the instantiations for the parameter '{term}' are not consistent: \n\n'{a}'\n\nand\n\n'{b}'"
            if self.rule_doc is not None:
                msg += f"\n\nRem reminds you of the rule.\n{self.rule_doc}"
            raise REM_CONSTRUCTION_Error(msg)
        
    def other_check(self, expr : bool, reason : str) -> None:
        '''
        If the `expr` does not hold, it will raise a formated error with information `reason`.
        This is intended for the check for correct operations.
        '''
        if not expr:
            msg = f"\n({self.name}): Rem does not accept because: \n\n{reason}"

            if self.rule_doc is not None:
                msg += f"\n\nRem reminds you of the rule.\n{self.rule_doc}"
            raise REM_CONSTRUCTION_Error(msg)


class RemSort(NetworkNode, RemNamed[T_Cons]):
    '''
    The sorts in Rem system.
    One important feature is that every sort itself can also be an algebra.
    '''

    def __init__(self, name : str, attr_pres : Dict[str, RemSort | Type] = {}, super_sorts : Tuple[RemSort, ...] = ()):
        
        self.__initialized = False

        RemNamed.__init__(self, name)
        NetworkNode.__init__(self, set())

        for sort in super_sorts:
            self.set_super_node(sort)

        if not isinstance(super_sorts, tuple):
            raise REM_META_Error(f"({self.name}): The super sorts should be a tuple.")
        
        for sort in super_sorts:
            if not isinstance(sort, RemSort):
                raise REM_META_Error(f"({self.name}): The super sort '{sort}' is not an instance of class RemSort.")
            

        # the prescription of term attributes
        if not isinstance(attr_pres, dict):
            raise REM_META_Error(f"({self.name}): The attribute prescription should be a dictionary.")
        
        self.__self_attr_pres = attr_pres.copy()
        
        self.__calc_attr_pres()

        # the documentation attribute
        self.doc : str | None = None

        # The extra check on term attributes. Reassign to redefine.
        self.attr_extra_check : Callable[[RemTerm, RemContext], None] | None = None

        self.__initialized = True

    @property
    def attr_names(self) -> Tuple[str, ...]:
        return tuple(self.__attr_pres.keys())

    def __calc_attr_pres(self):

        # inherit all the attribute prescriptions from super sorts

        all_attr_pres : Dict[str, RemSort | Type] = self.__self_attr_pres.copy()

        for sort in self.upstream_nodes:
            for attr in sort.__self_attr_pres:
                if attr not in all_attr_pres:
                    all_attr_pres[attr] = sort.__self_attr_pres[attr]
                elif all_attr_pres[attr] == sort.__self_attr_pres[attr]:
                    continue
                else:
                    raise REM_META_Error(f"Inconsistent extra attribute prescription: the attribute '{attr}' is already required to be '{all_attr_pres[attr]}', but still required to be '{sort.__self_attr_pres[attr]}' in '{sort}'.")
                    
        self.__attr_pres = all_attr_pres

    def set_super_node(self, super_node: Any):
        # TODO #3 change the super should triger recalculation of attribute prescriptions. But there are still bugs on this case when the situation is complicated.
        super().set_super_node(super_node)

        if self.__initialized:
            self.__calc_attr_pres()

    #######################################################
    # sort check - checking for valid terms of this sort

    def attr_pres_check(self, term : RemCons, ctx : RemContext):
        '''
        Checks that the term implements the attribute prescription of this sort.
        '''

        for attr in self.__attr_pres:

            try:
                attr_term = term[attr]

                if isinstance(self.__attr_pres[attr], RemSort):
                    self.type_check(attr_term, RemTerm, attr)
                    vt = RemVTerm.verify(attr_term, ctx)
                    if not vt.well_typed(self.__attr_pres[attr]):
                        raise REM_Sort_Error(attr_term, self.__attr_pres[attr])
                else:
                    self.type_check(attr_term, self.__attr_pres[attr], attr)

            except REM_CONSTRUCTION_Error:
                raise REM_CONSTRUCTION_Error(f"The term '{term}' does not implement the attribute prescription of '{self}':\n\nThe attribute '{attr}' is not defined.")
            

        # sort's extra check
        if self.attr_extra_check is not None:
            self.attr_extra_check(term, ctx)

    ########################################################
    # pretty printing
    def term_str(self, term : T_Cons) -> str:
        '''
        Return the default format string of the `term`.
        Reassign to modify.
        '''
        # default printing

        res = f"{term.fun.name}"
        if term.fun.arity == 0:
            res += f"()"
        else:
            res += f"({term[0]}"
            for i in range(1, term.fun.arity):
                res += f", {term[i]}"
            res += ")"
        return res
    

    def __eq__(self, __value: object) -> bool:
        '''
        Two sorts are considered identical only if they are the same Python object.
        '''
        return __value is self
    
    def __hash__(self) -> int:
        return id(self)
    
    def vlayout(self, dot: Digraph, id : str, title : str):
        dot.node(id, title,
            shape = "tab", style="filled", fillcolor = "gray",
            fontname = "Consolas",
            labeljust="l")
        

# the type hint for extract functions
ExtractFun = Callable[["RemCons"], object]

class RemFun(RemNamed, Generic[T_Cons]):
    '''
    The functions in Rem system.
    '''

    # this static attribute controls the type of constructed term
    term_type : Type[T_Cons]

    def __init__(self, name : str, para_sorts : Tuple[RemSort, ...], domain_sort : RemSort, extra_para_types : Dict[str, Type] | None = None):
        '''
        extra_para_types: types for extra parameters
        '''
        RemNamed.__init__(self, name)
        
        if not isinstance(para_sorts, tuple):
            raise REM_META_Error(f"({self.name}): The parameter sorts should be a tuple.")
        
        for sort in para_sorts:
            if not isinstance(sort, RemSort):
                raise REM_META_Error(f"({self.name}): The parameter sort '{sort}' is not an instance of class '{RemSort.__name__}'.")
        self.para_sorts : Tuple[RemSort, ...] = para_sorts

        # default para doc
        self.__para_doc : Tuple[str, ...] = tuple([f"para[{i}]" for i in range(self.arity)])
        

        # default extra para doc
        self.__extra_para_doc : Dict[str, str] = {}

        if extra_para_types is not None:
            if not isinstance(extra_para_types, dict):
                raise REM_META_Error(f"({self.name}): The extra parameter types should be a tuple.")
            
            for name in extra_para_types:
                type = extra_para_types[name]
                if not inspect.isclass(type):
                    raise REM_META_Error(f"({self.name}): The extra parameter type '{type}' is not a type.")
                
            for para in extra_para_types:
                self.__extra_para_doc[para] = str(extra_para_types[para])

        self.extra_para_types : Dict[str, Type] | None = extra_para_types

        if not isinstance(domain_sort, RemSort):
            raise REM_META_Error(f"({self.name}): The domain sort '{domain_sort}' is not an instance of class RemSort.")
        
        self.domain_sort   : RemSort = domain_sort

        # the precedence of this term. applied in parsing and printing
        self.precedence : None | Tuple[int, str] = None

        # the documentation attributes
        self.doc : str | None = None
        self.rule_doc : str | None = None


        # the function specific term printing. high priority. reassign to modify
        self.term_str : Callable[[RemCons], str] | None = None

        # the functions to extract the corresponding attribute
        # it will be invocated in the __getitem__ of RemCons instances, when a string index is passed in
        self.attr_extract : Dict[str, ExtractFun] = {}


    @property
    def arity(self) -> int:
        '''
        not include extra parameters
        '''
        return len(self.para_sorts)
    
    @property
    def terminal(self) -> bool:
        return len(self.para_sorts) == 0
    
    def set_para_doc(self, *para_doc : str) -> None:
        if len(para_doc) != self.arity:
            raise REM_META_Error(f"({self.name}): The parameter doc has {len(para_doc)} elements, which is inconsistent with the arity {self.arity}.")
        
    def set_extra_para_doc(self, **extr_para_doc : str) -> None:
        if self.extra_para_types is None:
            raise REM_META_Error(f"({self.name}): Not extra parameters.")
        
        for para in extr_para_doc:
            if para not in self.extra_para_types:
                raise REM_META_Error(f"({self.name}): '{para}' is not the name of an extra parameter.")
            self.__extra_para_doc[para] = extr_para_doc[para]

        
    ############################################################
    # parser setting

    def set_precedence(self, prec: int, assoc: str):
        self.precedence = (prec, assoc)
    

    ############################################################
    # common checkings

    
    def __call__(self, *paras : RemTerm | str, **kwparas) -> T_Cons:
        '''
        Create a `RemCons` instance with the parameters.
        It will not check sort related properties, which require a context.

        - paras: string elements are converted to variables
        '''

        # transform string to variables
        temp_paras = []
        for i in range(len(paras)):
            if isinstance(paras[i], str):
                temp_paras.append(RemVar(paras[i])) # type: ignore
            else:
                temp_paras.append(paras[i])
        paras = tuple(temp_paras)

        

        # check for parameters
        if len(paras) != self.arity:
            raise REM_CONSTRUCTION_Error(f"({self.name}): Invalid argument number. The function arity is {self.arity} but {len(paras)} arguments are provided.")
        
        for i in range(self.arity):
            self.type_check(paras[i], RemTerm, self.__para_doc[i])
        
        # check and add extra parameters        
        extra_attrs = {}
        if self.extra_para_types is not None:
            for para in self.extra_para_types:
                if para in self.attr_extract:
                    continue
                elif para in kwparas:
                    para_val = kwparas[para]
                    self.type_check(kwparas[para], self.extra_para_types[para], self.__extra_para_doc[para])

                    # assign the extra para
                    extra_attrs[para] = para_val
                else:
                    raise REM_CONSTRUCTION_Error(f"({self.name}): The extra parameter '{para}' is missing.")

        
        # extra check for parameters    
        self.extra_check(self, *paras, **kwparas)

        term : T_Cons = self.term_type(self, paras, extra_attrs)

        #  modification
        self.modify(term, *paras, **kwparas)

        return term

    # common checkings
    ###########################################################
    
    def extra_check(self, fun : RemFun, *paras : RemTerm, **kwparas):
        '''
        Extra validity check when constructing this term.
        (redefine to enable)
        '''
        pass

    def modify(self, term : T_Cons, *paras : RemTerm, **kwparas):
        '''
        The modification on the term to be created.
        (redefine to enable)
        '''
        pass

    def __eq__(self, __value: object) -> bool:
        '''
        Two functions are considered identical only if they are the same Python object.
        '''
        return __value is self
    
    def __hash__(self) -> int:
        return id(self)

    ##############################################
    # for pretty printing

    def enclosed(self, inner_str : str) -> str:
        '''
        Return the enclosed string of itself.
        Reload this method to redefine enclosing.
        '''
        return f"({inner_str})"


    def ctx_term_str(self, term : RemCons, super_fun : RemFun, left : bool = True) -> str:
        '''
        Use `ctx_str` instead of `__str__` to compose the printing when this term may need enclosing.

        According to the context of `super_fun`, decide whether enclose the string of itself, and return the result.
        - `left`: for binary operators only. whether this term is the left one or the right one.
        '''

        if super_fun.precedence is None or term.fun.precedence is None:
            return str(term)
        elif super_fun.precedence[0] > term.fun.precedence[0]:
            return term.fun.enclosed(str(term))
        elif super_fun.precedence[0] < term.fun.precedence[0]:
            return str(term)
        else:
            # equal precedence
            if (term.fun.precedence[1] == 'left' and left == False)\
            or (term.fun.precedence[1] == 'right' and left == True):
                return term.fun.enclosed(str(term))
            else:
                return str(term)


    ###################################################
    # drawing by Graphviz

    def vlayout(self, dot : Digraph, id : str, title : str):

        # visual distinction between terminal/nonterminals
        if self.terminal:
            dot.node(id, title,
                shape = "note", style="filled", fillcolor = "gray",
                fontname = "Consolas",
                labeljust="l")
        else:
            dot.node(id, title,
                shape = "cds", style="filled", fillcolor = "gray",
                fontname = "Consolas",
                labeljust="l")


class RemTerm(RemObject):
    '''
    A term in the signature, including:
        - RemVar (variable)
        - RemCons (function symbol)
    '''

    def __setattr__(self, __name: str, __value: Any) -> None:
        return super().__setattr__(__name, __value)

    ################################################
    # universal algebra methods
    
    
    def pos(self, pos : str) -> RemTerm:
        '''
        Get the subterm at the specified position.
        - `pos`: Empty string represents root. Parameter index starts from `0`.
        (It only supports parameter number less than 10, but I think it's sufficient for now.)
        '''
        raise NotImplementedError()
    
    @property
    def size(self) -> int:
        '''
        Return the size of the abstract syntax tree.
        '''
        raise NotImplementedError()
    
    def variables(self) -> set[str]:
        '''
        Return a set of (the name of) all variables in this term.
        '''
        raise NotImplementedError()

    @property
    def ground(self) -> bool:
        return len(self.variables()) == 0
    
    def substitute(self, sigma : RemSubst) -> RemTerm:
        '''
        The substitution will preserve well-typed proof when possible.
        '''
        raise NotImplementedError()
    
    
    ################################################

    def __getitem__(self, i : int | str) -> Any:
        '''
        This syntax sugar imitate the positioning in universal algebra
        '''
        raise REM_CONSTRUCTION_Error(f"Cannot access the attributes of term '{self}'.")


    ########################################
    # printing
    
    def ctx_term_str(self, super_fun : RemFun, left : bool = True) -> str:
        return str(self)

    def vlayout(self, dot: Digraph, id: str, title: str):
        raise NotImplementedError()

    def ast_vlayout(self, dot: Digraph, traveled : set[RemTerm]):
        '''
        The traveled nodes will not be drawn again.
        '''
        raise NotImplementedError()

    def ast_draw(self, output : str | None = None, labelled : bool = True) -> Digraph:
        '''
        draw the abstruct syntax tree of the term
        '''
        dot = Digraph()
        self.ast_vlayout(dot, set())
        
        if labelled:
            # add the label
            dot.graph_attr["label"] = str(self)
            dot.graph_attr["fontname"] = "Consolas"
            dot.graph_attr["labelloc"] = "t"


        if output is not None:
            dot.render(output, cleanup=True, engine='dot')


        return dot

            

class RemVar(RemTerm):
    def __init__(self, var : str):
        self.__var = var
    
    @property
    def var(self) -> str:
        return self.__var
    
    def __eq__(self, __value: object) -> bool:
        if isinstance(__value, RemVar):
            return self.__var == __value.__var
        else:
            return False
        
    def __hash__(self) -> int:
        return hash(self.__var)
    
    def __str__(self) -> str:
        return self.__var
    

    ############################################################
    # universal algebra methods
    
    def pos(self, pos : str) -> RemVar:
        if pos == "":
            return self
        else:
            raise REM_CONSTRUCTION_Error(f"Invalid position '{pos}' for term '{self}'.")
        
    @property
    def size(self) -> int:
        return 1
    
    def variables(self) -> set[str]:
        return {self.__var}
    
    def substitute(self, sigma: RemSubst) -> RemTerm:
        if self.__var in sigma:
            return sigma[self.__var]
        else:
            return self


    ############################################################
    
    def vlayout(self, dot: Digraph, id: str, title: str):
        dot.node(id, title,
            shape = "circle", style="filled", fillcolor = "gray",
            fontname = "Consolas",
            labeljust="l")
        
    def ast_vlayout(self, dot: Digraph, traveled : set[RemTerm]):
        self.vlayout(dot, self.graphvizID, str(self))

            


class RemCons(RemTerm):
    '''
    Terms from function application
    '''
    def __init__(self, fun : RemFun, paras : Tuple[RemTerm, ...], extra_attrs : Dict[str, Any]):
        '''
        This constructor should not be invocated manually.
        '''
        self._fun = fun
        self._paras = paras
        self._extra_attrs = extra_attrs.copy()

    def copy(self) -> RemCons:
        return copy.copy(self)
    
    @property
    def sort_attr_name(self):
        return self.fun.domain_sort.attr_names
    
    @property
    def extra_attrs(self) -> tuple:
        return tuple([self[name] for name in self.sort_attr_name])
        
        
    @property
    def fun(self) -> RemFun:
        return self._fun
    
    @property
    def paras(self) -> Tuple[RemTerm, ...]:
        return self._paras
    
    def __getitem__(self, i : int | str) -> Any:
        '''
        This syntax sugar imitate the positioning in universal algebra
        '''
        if isinstance(i, int):
            return self._paras[i]
        
        # resort to parameter naming from the function symbol
        elif isinstance(i, str):
            if i in self.fun.attr_extract:
                return self.fun.attr_extract[i](self)

            elif i in self._extra_attrs:
                return self._extra_attrs[i]
                
            else:
                raise REM_CONSTRUCTION_Error(f"The attribute of name '{i}' does not exist for function '{self.fun}'.")
        
        else:
            raise Exception()
        
    def __setitem__(self, i : str, value):
        self._extra_attrs[i] = value
    
    def __eq__(self, __value: object) -> bool:
        if __value is self:
            return True
        elif isinstance(__value, RemCons):
            if __value._fun == self._fun and __value._paras == self._paras and __value.extra_attrs == self.extra_attrs:

                # the extracted attributes should be identical too
                for attr in self.fun.attr_extract:
                    if self[attr] != __value[attr]:
                        return False
                return True
            
            else:
                return False



        else:
            return False
        
    def __hash__(self) -> int:
        res = hash(self._fun)

        for para in self._paras:
            res ^= hash(para)

        # The hash value may collide when two terms only differ in extra attributes. We leave this situation to the `__eq__` function.
        return res

    ############################################################
    # universal algebra methods

    def pos(self, pos : str) -> RemTerm:
        if pos == "":
            return self
        else:
            if int(pos[0]) < self.fun.arity:
                return self._paras[int(pos[0])].pos(pos[1:])
            else:
                raise REM_CONSTRUCTION_Error(f"Invalid position '{pos}' for term '{self}'.")
            
    @property
    def size(self) -> int:
        res = 1
        for para in self._paras:
            res += para.size
        return res
    
    def variables(self) -> set[str]:
        res = set()
        for para in self._paras:
            res |= para.variables()

        return res
    
    def substitute(self, sigma: RemSubst) -> RemCons:
        '''
        The extra attributes will not be substituted.
        '''
        res = self.copy()

        new_paras = []
        for i in range(len(res._paras)):
            new_paras.append(res._paras[i].substitute(sigma))

        res._paras = tuple(new_paras)

        return res
        

    def replace(self, i : int, subterm : RemTerm) -> RemTerm:
        '''
        replace the i-th parameter with the new subterm and return the result
        '''
        res = self.copy()
        res._paras = res._paras[:i] + (subterm,) + res._paras[i+1:]
        
        return res

    ############################################################


    def __str__(self) -> str:
        '''
        The formatted string of a term is determined by the function.
        '''
        if self.fun.term_str is not None:
            return self.fun.term_str(self)
        else:
            return self.fun.domain_sort.term_str(self)
    
    def ctx_term_str(self, super_fun : RemFun, left : bool = True) -> str:
        return self.fun.ctx_term_str(self, super_fun, left)
    
    def vlayout(self, dot: Digraph, id : str, title : str):
        dot.node(id, title,
            shape = "box", style="filled", fillcolor = "gray",
            fontname = "Consolas",
            labeljust="l")
        
    def ast_vlayout(self, dot: Digraph, traveled : set[RemTerm]):
        # function symbol as node
        if self in traveled:
            return
        
        traveled.add(self)
        self._fun.vlayout(dot, self.graphvizID, str(self._fun))

        for i in range(len(self._paras)):
            para = self._paras[i]
            para.ast_vlayout(dot, traveled)

            # subterm as edge
            dot.edge(self.graphvizID, para.graphvizID, label = str(i), fontname = "Consolas")
        
        # append the extra parameters (if exist)
        if self._fun.extra_para_types is not None:
            for para_name in self._fun.extra_para_types:
                para = getattr(self, para_name)
                dot.node(str(id(para)), str(para), shape = "plain", 
                fontname = "Consolas",
                labeljust="l")

                # subterm as edge
                dot.edge(self.graphvizID, str(id(para)), label = para_name, fontname = "Consolas")


RemFun.term_type = RemCons # type: ignore

#########################################################
# verified terms


# the type of contexts for the order sorted algebra
class RemContext:
    '''
    The content of a RemContext cannot be modified.
    '''
    def __init__(self, data : Dict[str, RemSort] = {}):
        self._data = data.copy()

    @property
    def data(self) -> Dict[str, RemSort]:
        return self._data.copy()

    def __le__(self, other) -> bool:
        if self is other:
            return True
        elif isinstance(other, RemContext):
            for key in self._data:
                if key not in other._data or self._data[key] != other._data[key]:
                    return False
                
            return True
        
        else:
            return False
    
    def __eq__(self, other) -> bool:
        if self is other:
            return True
        elif isinstance(other, RemContext):
            return self._data == other._data
        else:
            return False
        
    def __contains__(self, idx) -> bool:
        return idx in self._data

    def __getitem__(self, idx) -> RemSort:
        return self._data[idx]
    
    def __str__(self) -> str:

        if len(self._data.keys()) == 0:
            return "[]"
        
        res = "["

        for key in self._data:
            res += f"{key} : {self._data[key]}; "
        return res[:-2] + "]"


class RemVTerm:
    def __init__(self, term : RemTerm, ctx : RemContext):
        '''
        The constructor does not check validity of the well-typed term.
        '''
        self._term = term
        self._ctx = ctx

    @staticmethod
    def verify(term : RemTerm, ctx : RemContext = RemContext()) -> RemVTerm:
        '''
        Check the validity of the well-typed term in the context and return the verified term.
        '''

        if isinstance(term, RemVar):
            if not term.var in ctx:
                raise REM_CONSTRUCTION_Error(f"Well-typed term cannot be constructed. Variable '{term.var}' is not defined in the context.")

            return RemVTerm(term, ctx)
        
        elif isinstance(term, RemCons):

            # check the subterms
            for i in range(term.fun.arity):
                vt = RemVTerm.verify(term.paras[i], ctx)

                if not vt.well_typed(term.fun.para_sorts[i]):
                    raise REM_Sort_Error(term.paras[i], term.fun.para_sorts[i])
                
            # check the implementation of attribute prescriptions. note that extra Rem terms are check w.r.t. the same context
            term.fun.domain_sort.attr_pres_check(term, ctx)

            return RemVTerm(term, ctx)
        
        else:
            raise Exception()

        
    
    @property
    def term(self) -> RemTerm:
        return self._term
    
    @property
    def ctx(self) -> RemContext:
        return self._ctx
    
    @property
    def sort(self) -> RemSort:
        if isinstance(self._term, RemVar):
            return self._ctx[self._term.var]
        elif isinstance(self._term, RemCons):
            return self._term.fun.domain_sort
        else:
            raise Exception()
        

    def well_typed(self, sort: RemSort) -> bool:
        '''
        only verified terms can check the well-typed proof
        '''
        return sort in self.sort.upstream_nodes
    
    def __getitem__(self, i) -> Any:
        return self._term[i]
    
    def __getattribute__(self, __name: str) -> Any:
        '''
        The attributes of the verified term can be directly accessed.
        '''
        try:
            return object.__getattribute__(self, __name)
        except AttributeError:
            return object.__getattribute__(self._term, __name)
    
    def __str__(self) -> str:
        return str(self.term)
    
    def full_str(self) -> str:
        return f"{self.ctx} ⊢ {self.term} : {self.sort}"



#########################################################
# substitutions

T_sub = TypeVar("T_sub", "RemSubst", RemTerm)

class RemSubst:
    def __init__(self, data : Dict[str, RemTerm]):
        self._data = data.copy()

    def copy(self) -> RemSubst:
        return RemSubst(self._data)

    @property
    def data(self) -> Dict[str, RemTerm]:
        return self._data.copy()

    def __call__(self, term : T_sub) -> T_sub:
        '''
        Apply the substitution on a term. Return the result.
        '''
        if isinstance(term, RemTerm):
            return term.substitute(self)
        elif isinstance(term, RemSubst):
            return self.composite(term)
        else:
            raise REM_META_Error("Invalid application of substitution.")
    
    def __contains__(self, idx) -> bool:
        return idx in self._data

    def __getitem__(self, idx) -> RemTerm:
        return self._data[idx]
    
    def __str__(self):
        if len(self._data.keys()) == 0:
            return "{}"
        
        res = "{"
        for key in self._data:
            res += f"{key} ↦ {self._data[key]}, "
        return res[:-2] + "}"
    
    def __eq__(self, other) -> bool:
        if self is other:
            return True
        
        if isinstance(other, RemSubst):
            return self._data == other._data
        
        else:
            return False
    

    ################################################
    # universal algebra methods
    
    @property
    def domain(self) -> set[str]:
        return set(self._data.keys())

    @property
    def range(self) -> set[RemTerm]:
        return set(self._data.values())
    
    @property
    def vrange(self) -> set[str]:
        res = set()
        for rhs in self._data.values():
            res |= rhs.variables()
        return res
    
    def composite(self, other : RemSubst) -> RemSubst:
        '''
        return the composition `self(other)`.
        '''
        new_data = {}

        for var in other.domain:
            new_data[var] = other[var].substitute(self)

        for var in self.domain - other.domain:
            new_data[var] = self[var]

        return RemSubst(new_data)
    
    @property
    def idempotent(self) -> bool:
        '''
        A substitution σ is idempotent if σ = σσ.
        '''
        # This is the equivalent condition for idempotent
        return len(self.domain & self.vrange) == 0
    

class RemUnification:
    '''
    A unification problem in Rem system.
    (No type check.)
    '''
    def __init__(self, eqs : List[Tuple[RemTerm, RemTerm]]):
        self.eqs = eqs

    def __str__(self) -> str:
        if len(self.eqs) == 0:
            return "{}"
        
        res = "{"
        for lhs, rhs in self.eqs:
            res += f"{lhs} =? {rhs}, "
        return res[:-2] + "}"
    
    @property
    def variables(self) -> set[str]:
        res = set()
        for lhs, rhs in self.eqs:
            res |= lhs.variables() | rhs.variables()
        return res        
    
    @property
    def solved(self) -> bool:
        '''
        Check whether the unification problem is in the solved form.
        '''
        var_set : set[str] = set()
        for eq in self.eqs:
            if isinstance(eq[0], RemVar):
                if eq[0].var in var_set:
                    return False
                else:
                    var_set.add(eq[0].var)
            else:
                return False
            
        # none of them appear on the right
        for eq in self.eqs:
            if len(var_set & eq[1].variables()) > 0:
                return False
            
        return True
    

    def solve(self) -> RemSubst | None:
        '''
        Reduce the problem and 

        Based on [Term Rewriting and All That] Sec.4.5, Syntactic Unification.
        '''

        eqs = self.eqs.copy()

        while True:

            modified = False
            for i in range(len(eqs)):
                lhs, rhs = eqs[i]

                # Delete
                if lhs == rhs:
                    eqs = eqs[:i] + eqs[i+1:]

                    modified = True
                    break

                if isinstance(lhs, RemCons) and isinstance(rhs, RemCons):
                    # Decompose
                    if lhs.fun == rhs.fun:
                        eqs = eqs[:i] + eqs[i+1:]
                        for i in range(lhs.fun.arity):
                            eqs.append((lhs.paras[i], rhs.paras[i]))

                        modified = True
                        break
                            
                    # Clash
                    else:
                        return None
                
                # Orient
                if isinstance(rhs, RemVar) and not isinstance(lhs, RemVar):
                    eqs[i] = (rhs, lhs)

                    modified = True
                    break

                if isinstance(lhs, RemVar): 

                    # calculate the variable of the rest equations
                    varS = set()
                    for j in range(len(eqs)):
                        if j != i:
                            _lhs, _rhs = eqs[j]
                            varS |= _lhs.variables() | _rhs.variables()
                    
                    # Eliminate
                    if lhs.var in (varS - rhs.variables()):
                        sub = RemSubst({lhs.var : rhs})
                        for j in range(len(eqs)):
                            if j != i:
                                _lhs, _rhs = eqs[j]
                                eqs[j] = (sub(_lhs), sub(_rhs))

                        modified = True
                        break

                    # Occurs-Check
                    if lhs.var in rhs.variables() and lhs != rhs:
                        return None
                    
            if not modified:
                break
                
        assert RemUnification(eqs).solved

        sol = {}
        for lhs, rhs in eqs:
            assert isinstance(lhs, RemVar)
            sol[lhs.var] = rhs

        return RemSubst(sol)



class RemMatching:
    '''
    A matching problem in Rem system.
    (No type check.)

    Based on [Term Rewriting and All That] Sec.4.7
    '''
    def __init__(self, ineqs : List[Tuple[RemTerm, RemTerm]]):
        self.ineqs = ineqs

    def __str__(self) -> str:
        if len(self.ineqs) == 0:
            return "{}"
        
        res = "{"
        for lhs, rhs in self.ineqs:
            res += f"{lhs} ≲? {rhs}, "
        return res[:-2] + "}"
    
    @property
    def variables(self) -> set[str]:
        res = set()
        for lhs, rhs in self.ineqs:
            res |= lhs.variables() | rhs.variables()
        return res        
    
    def solve(self) -> RemSubst | None:
        ineqs = self.ineqs.copy()

        subst : Dict[str, RemTerm] = {}

        while len(ineqs) > 0:
            lhs, rhs = ineqs[0]

            if isinstance(lhs, RemVar):
                if lhs.var in subst.keys():
                    if RemSubst(subst)(lhs) == rhs:
                        ineqs = ineqs[1:]
                        continue
                    else:
                        return None
                else:
                    subst[lhs.var] = rhs
                    ineqs = ineqs[1:]
                    continue

            elif isinstance(lhs, RemCons):
                if isinstance(rhs, RemVar):
                    return None
            
                elif isinstance(rhs, RemCons):
                    if lhs.fun == rhs.fun:
                        ineqs = ineqs[1:]
                        for i in range(lhs.fun.arity):
                            ineqs.append((lhs.paras[i], rhs.paras[i]))
                        continue

                    else:
                        return None
                else:
                    raise Exception()
                
            else:
                raise Exception()
                    
        return RemSubst(subst)


    @staticmethod
    def single_match(lhs : RemTerm, rhs : RemTerm) -> RemSubst | None:
        return RemMatching([(lhs, rhs)]).solve()