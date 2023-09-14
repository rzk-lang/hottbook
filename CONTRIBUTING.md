# Contribution guide

Thank you for contributing to formalizations of the HoTT Book in rzk! In order to better organize the work it's better to follow these guidelines.

## Formalizing section definitions

The repository follows the structure of the book. 
Definitions introduced in section *N.M \<SECTION_NAME\>* of *Chapter N. \<CHAPTER_NAME\>* (*Part L \<PART_NAME\>*) are to be placed in file `src/L-<PART_NAME>/N-<CHAPTER_NAME>/M-<SECTION_NAME>.rzk.md`.

For example, section *1.5 Product types* in chapter *1 Type theory* (part *1 Foundations*) corresponds to `src/1-foundations/1-type-theory/05-product-types.rzk.md`

To avoid conflicts and simplify the review, it is encouraged to create a separate branch and PR for each section.

Branches should be named in the format `N.M-*`. For example, `1.6-induction-definition`.

## Solving exercises

Solutions for exercises are grouped by chapter in corresponding `*chapter*/exercises/` folder.

Similarly, it is preferred to create a separate PR for each exercise.

Branches should be named in the format `ex-A.B-*`. For example, `ex-1.1-full-solution`.

