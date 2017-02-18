<!-- build with: pandoc --filter pandoc-citeproc -N --toc --latex-engine=xelatex -->

---
monofont: DejaVu Sans Mono
bibliography: [alti.bib, local.bib]
link-citations: true

header-includes:
   - \setlength\parindent{12pt}
   - \usepackage{amsthm}
   - \usepackage{indentfirst}
   - \newtheorem{theorem}{Theorem}

title: 
  A Machine-Checked Correctness Proof of Normalization by Evaluation
  for Simply Typed Lambda Calculus
author: 
- 'Author: András Kovács'
- 'Advisor: Ambrus Kaposi'
date: Budapest, 2016
abstract: Lorem ipsum dolor sit amet, consectetur adipiscing elit, sed do eiusmod tempor incididunt ut labore et dolore magna aliqua. Ut enim ad minim veniam, quis nostrud exercitation ullamco laboris nisi ut aliquip ex ea commodo consequat. Duis aute irure dolor in reprehenderit in voluptate velit esse cillum dolore eu fugiat nulla pariatur. Excepteur sint occaecat cupidatat non proident, sunt in culpa qui officia deserunt mollit anim id est laborum.
---

# Random header

Code block:

~~~agda

  infixr 4 _⇒_
  
  data Ty : Set where
    ι   : Ty
    _⇒_ : Ty → Ty → Ty
  
  data Con : Set where
    ∙   : Con
    _,_ : Con → Ty → Con
  
  data _∈_ (A : Ty) : Con → Set where
    vz : ∀ {Γ} → A ∈ (Γ , A)
    vs : ∀ {B Γ} → (v : A ∈ Γ) → A ∈ (Γ , B)
  
  data Tm Γ : Ty → Set where
    var : ∀ {A} → (v : A ∈ Γ) → Tm Γ A
    lam : ∀ {A B} → Tm (Γ , A) B → Tm Γ (A ⇒ B)
    app : ∀ {A B} → (f : Tm Γ (A ⇒ B)) → (a : Tm Γ A) → Tm Γ B
~~~

Now let's try some inline code: `∀ a → a ∈ Γ → a ≢ foo`{.agda}.


## Random header again

Lorem ipsum dolor sit amet, consectetur adipiscing elit, sed do eiusmod tempor incididunt ut labore et dolore magna aliqua. Ut enim ad minim veniam, quis nostrud exercitation ullamco laboris nisi ut aliquip ex ea commodo consequat. Duis aute irure dolor in reprehenderit in voluptate velit esse cillum dolore eu fugiat nulla pariatur. Excepteur sint occaecat cupidatat non proident, sunt in culpa qui officia deserunt mollit anim id est laborum.

Duis aute irure dolor in reprehenderit in voluptate velit esse cillum dolore eu fugiat nulla pariatur. Excepteur sint occaecat cupidatat non proident, sunt in culpa qui officia deserunt mollit anim id est laborum.
\
\begin{theorem}
Lorem ipsum dolor sit amet, consectetur adipiscing elit, sed do eiusmod tempor incididunt ut labore et dolore magna aliqua. Ut enim ad minim veniam, quis nostrud exercitation ullamco laboris nisi ut aliquip ex ea commodo consequat.
\end{theorem}

\begin{proof}
Lorem ipsum dolor sit amet, consectetur adipiscing elit, sed do eiusmod tempor incididunt ut labore et dolore magna aliqua. Ut enim ad minim veniam, quis nostrud exercitation ullamco laboris nisi ut aliquip ex ea commodo consequat. Duis aute irure dolor in reprehenderit in voluptate velit esse cillum dolore eu fugiat nulla pariatur. Excepteur sint occaecat cupidatat non proident, sunt in culpa qui officia deserunt mollit anim id est laborum.
\end{proof}

Some linky thing [here](#random-header-again). H~2~O is a liquid.  2^10^ is 1024.

~~~agda
  data Tm Γ : Ty → Set where
    var : ∀ {A} → (v : A ∈ Γ) → Tm Γ A
    lam : ∀ {A B} → Tm (Γ , A) B → Tm Γ (A ⇒ B)
    app : ∀ {A B} → (f : Tm Γ (A ⇒ B)) → (a : Tm Γ A) → Tm Γ B
~~~


1. fruits
    + apples
        - macintosh
        - red delicious
    + pears
    + peaches
1. vegetables
    + broccoli
    + chard
    
    
Apple
:   Pomaceous fruit of plants of the genus Malus in 
    the family Rosaceae.

Orange
:   The fruit of an evergreen tree of the genus Citrus.


(@)  My first example will be numbered (1).
(@)  My second example will be numbered (2).

Explanation of examples.

(@)  My third example will be numbered (3).


  Right     Left     Center     Default
-------     ------ ----------   -------
     12     12        12            12
    123     123       123          123
      1     1          1             1

Table:  Demonstration of simple table syntax.


-------------------------------------------------------------
 Centered   Default           Right Left
  Header    Aligned         Aligned Aligned
----------- ------- --------------- -------------------------
   First    row                12.0 Example of a row that
                                    spans multiple lines.

  Second    row                 5.0 Here's another one. Note
                                    the blank line between
                                    rows.
-------------------------------------------------------------

Table: Here's the caption. It, too, may span
multiple lines.


: Sample grid table.

+---------------+---------------+--------------------+
| Fruit         | Price         | Advantages         |
+===============+===============+====================+
| Bananas       | $1.34         | - built-in wrapper |
|               |               | - bright color     |
+---------------+---------------+--------------------+
| Oranges       | $2.10         | - cures scurvy     |
|               |               | - tasty            |
+---------------+---------------+--------------------+


| Right | Left | Default | Center |
|------:|:-----|---------|:------:|
|   12  |  12  |    12   |    12  |
|  123  |  123 |   123   |   123  |
|    1  |    1 |     1   |     1  |

  : Demonstration of pipe table syntax.

Lorem ipsum dolor sit amet, consectetur adipiscing elit, sed do eiusmod tempor incididunt ut labore et dolore magna aliqua. Ut enim ad minim veniam, quis nostrud exercitation ullamco laboris nisi ut aliquip ex ea commodo consequat. Duis aute irure dolor in reprehenderit in voluptate velit esse cillum dolore eu fugiat nulla pariatur. Excepteur sint occaecat cupidatat non proident, sunt in culpa qui officia deserunt mollit anim id est laborum. Here is a footnote reference,[^1] and another[^longnote]. Here is an inline note.^[Inlines notes are easier to write, since
you don't have to pick an identifier and move down to type the
note.]

[^1]: Here is the footnote.

[^longnote]: Here's one with multiple blocks. Subsequent paragraphs are indented to show that they belong to the previous footnote. The whole paragraph can be indented, or just the first line.  In this way, multi-paragraph footnote work like multi-paragraph list items.


This paragraph won't be part of the note, because it
isn't indented. Here's a reference [@alti:tlca93]. Here's another [@alti:ctcs95].
And yet another here [@alti:csl98].

More references abound [@book; @devriese; @Palsberg; @mcbride2008applicative].

# References


