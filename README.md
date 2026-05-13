# $\mathsf{MA}^\omega$-Checker

The present project is a proof checker for proofs in the theory $MA^\omega$.
It is a part of my project “Material Interpretation” ([10.55776/ESP576](https://www.fwf.ac.at/forschungsradar/10.55776/ESP576)), funded by the FWF, to whom I would like to express my sincere gratitude.

## Background

The proof checker was written to address an open problem, namely the characterization of all formulas in
$\mathsf{MA}^\omega$ for which $D^{\mathbf{F}}\to D$ is provable. The goal would be to transform a description of these formulas into a proof, and vice versa.
A major partial success would already be an extension of this class of formulas $\mathcal{D}$, as described for example in [1,2].
In particular, this open question arose in the context of Friedman’s A-translation and is discussed in particular in Section 7.3.1 of [2].
A detailed presentation of the theory MA and the A-translation is given in particular in [1].
The Rust programming language was chosen to explore how well Rust is suited as a programming language for proofs.
The project is currently under development. I am very grateful for any comments or suggestions for improvement.

## Approach to the $\mathsf{MA}^\omega$-Checker

### Types

Types are defined in $\texttt{types.rs}$.
In the implementation, types are represented by an enum.
In shorthand notation, types $\tau, \rho$ can be defined syntactically as follows:

$$\tau,\rho ::= \xi \mid \mathbb{B} \mid \mathbb{N} \mid \mathbb{L}(\tau) \mid \tau \to \rho  \mid \tau \times \rho.$$

Here, $\xi$ denotes a type variable.
In the theory $\mathsf{MA}^\omega$, there are infinitely many type variables.
In the implementation, a type variable is represented by a $\texttt{usize}$.

### Terms

Terms in $\mathsf{MA}^\omega$ always come with a type.
Terms are formed from variables, constants, abstraction, and application.
In our implementation, terms are defined in the $\texttt{terms}$ folder.

#### Termvariables
Term variables, also called object variables, are defined as a struct in $\texttt{obj}\underline{ }\texttt{var.rs}$.
An object variable is given by its ID, a $\texttt{usize}$, and its type.
Optionally, one can also give the variable a name, a $\texttt{String}$, in order to obtain more readable output.
Two variables are equal if their ID and type agree. The name is irrelevant.

#### Constants
Constants are initially syntactic expressions and are represented by an $\texttt{enum}$, given in $\texttt{consts.rs}$.
Typical constants are 0, the successor, the case operator, and the recursion operators over natural numbers or lists.
Some constants take types as parameters. The method $\texttt{ty}$ returns the type of a constant.

#### Recursive definition of terms
In $\mathtt{term}\underline{ }\mathtt{kind.rs}$, term kinds are first defined recursively as syntactic objects by an $\texttt{enum}$.
Term kinds consist of constants, variables, the application of two term kinds, or the abstraction of a variable from a term kind
For term kinds, it does not matter whether everything is well-typed.

(Typed) terms are then defined in $\mathtt{typed}\underline{ }\mathtt{terms.rs}$.
They are represented by a struct consisting of a term kind and a type.
The individual components of the Term struct are private, so that terms can only be introduced through the methods provided in $\mathtt{typed}\underline{ }\mathtt{terms.rs}$.

Equality of term kinds, and hence also of terms, is defined in such a way that it also captures $\alpha$-equivalence.
The idea behind this definition goes back to [4].

### Formulas
Formulas are represented as an $\texttt{enum}$ in $\texttt{formula.rs}$.
There are atomic formulas, which are given by a term,
implication, conjunction, universal quantification, and the symbol $\bot$.
It should be noted here that, in the theory $\mathsf{MA}^\omega$, the term occurring in an atomic formula must have type Bool.
In the implementation, however, the type of the corresponding term is not checked at first.
Since Formula is a public $\texttt{enum}$, the user can turn any term into an atomic formula.
The user should therefore take care when using it.
However, the method $\texttt{atom}$ first checks whether the term is Boolean and returns a type error otherwise.

### Proofs
Proofs are structured similarly to terms. Formulas play for proofs the role that types play for terms.
The folder $\texttt{proofs}$, in which proofs are defined, therefore has a structure similar to the folder $\texttt{terms}$.

#### Assumptions

Assumptions are represented as a $\texttt{struct}$ in assumptions.rs.
They consist of an ID, given by a $\texttt{usize}$, a formula, and an optional name as a $\texttt{String}$.
Equality of assumptions is determined by the ID and the formula. The name is irrelevant for equality.

#### Axioms
Axioms are given as an $\texttt{enum}$.
These include the axiom $\mathsf{Truth}$, $\bot^+$, case distinction, and recursion.
Case distinction and recursion each take an object variable and a formula as arguments.
For case distinction, the object variable must have Boolean type,
while for recursion it must have either the type of natural numbers or a list type.
This can be seen from the method $\texttt{form}$,
which returns the formula corresponding to the given axiom,
or a type error if the above conditions are not satisfied.

#### Recursive definition of proofs
As with terms, we first define proof kinds recursively as syntactic objects by means of an $\texttt{enum}$ in $\mathtt{proof}\underline{ }\mathtt{kind.rs}$.
Proof kinds consist of assumptions, axioms, two kinds of application of two proof kinds to each other 
(once for conjunction introduction and once for implication elimination)
the abstraction of an assumption from a proof kind,
the abstraction of an object variable from a proof kind,
the application of a term to a proof kind,
and two forms of conjunction elimination applied to a proof kind.
In the case of proof kinds, the formula does not yet play a role.

Proofs themselves are then given in $\mathtt{checked}\underline{ }\mathtt{proofs.rs}$ as a $\texttt{struct}$ consisting of a proof kind and the corresponding formula.
Since the fields of $\texttt{Proof}$ are private, outside of the defining module instances can only be created through public constructor functions that enforce the correctness conditions.
In addition to the standard functions, the function efq is particularly worth mentioning: it takes a formula $A$ and returns a proof of $\mathsf{atom}(\mathsf{ff}) \to A$.

### Substitution

## Definite, Goal, Relevant and Irrelevant Formulas

## References 
[1] Trifon Trifonov, *Analysis of Methods for Extraction of Programs from Non-Constructive Proofs*, PhD thesis, Ludwig Maximilian University of Munich, 2012. DOI: [10.5282/EDOC.14030](https://doi.org/10.5282/edoc.14030). 

[2] Helmut Schwichtenberg and Stanley S. Wainer, *Proofs and Computations*, Cambridge University Press, 2012. DOI: [10.1017/CBO9781139031905](
   https://doi.org/10.1017/CBO9781139031905).

[3] Ulrich Berger, Wilfried Buchholz, and Helmut Schwichtenberg, “Refined program extraction from classical proofs,” *Annals of Pure and Applied Logic* 114(1–3), 3–25, 2002. DOI: [10.1016/S0168-0072(01)00073-2](https://doi.org/10.1016/S0168-0072(01)00073-2).

[4] Nicolaas Govert de Bruijn, “Lambda calculus notation with nameless dummies, a tool for automatic formula manipulation, with application to the Church-Rosser theorem,” *Indagationes Mathematicae (Proceedings)* 75(5), 381–392, 1972. DOI: [10.1016/1385-7258(72)90034-0](https://doi.org/10.1016/1385-7258(72)90034-0).
