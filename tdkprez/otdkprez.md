
---
build: pandoc -t beamer -F pandoc-citeproc otdkprez.md -o otdkprez.pdf --pdf-engine=xelatex
bibliography: references.bib
csl: ieee.csl
monofont: DejaVu Sans Mono
header-includes:
title:
  Az egyszerűen típusozott lambda kalkulus kiértékeléses normalizálásának
  formális helyességbizonyítása
author:
- 'Szerző: Kovács András'
- 'Témavezető: Kaposi Ambrus'
institute: Eötvös Loránd Tudományegyetem
date: 2019

---

## Eredmények

::: incremental

* Egyszerű típusos lambda kalkulus $\beta\eta$-normalizálása.

* A leírt algoritmus helyessége formálisan verifikált, Agda rendszerben.

* Korábbi hasonló formalizálásoknál lényegesen tömörebb,
  hatékony algoritmusra és standard (tankönyvi) szintaxisra.

:::

## Egyszerű típusos lambda kalkulus (STLC)

Magasabbrendű függgvények minimális programozási nyelve.\
\

. . .

Informális példák kifejezésekre:

~~~{.agda}
  λ (x : ι). x
  λ (f : ι → ι). λ (g : ι → ι). λ (x : ι). f (g x)
  (λ (f : ι → ι). f) (λ (x : ι) → x)
~~~
\

. . .

Normálformák: nem végezhető el több függvényalkalmazás és $\eta$-kifejtés.\
\

. . .

Normalizálás jelentősége más területeken: logika, kategóriaelmélet, típusellenőrzés polimorf és függő típusos nyelvekhez.

## Kiértékeléses normalizálás

Normalization-by-evaluation (NbE).\
\

. . .

Alapötlet: naiv helyettesítések helyett használjunk hatékony absztrakt gépet,
a szintaxist kiértékeljük futásidejű objektumokra, majd ebből a normálformákat
visszaolvassuk.\
\

. . .

A zárt funkcionális programok standard kiértékelését (pl. GHC, OCaml) általánosítja
nyílt (szabad változókat tartalmazó) programokra.

## Helyesség fogalma

Három feltétel egy normálformákat visszaadó függvényre:\
\

. . .

> (#) Complete: a függvény kimenete $\beta\eta$-ekvivalens a bemenettel.
> (#) Sound: a függvény $\beta\eta$-ekvivalens bemeneteket azonos kimenetre képez.
> (#) Stable: a függvény nem csinál semmit, ha az input eleve normálforma.

. . .

A három feltételből következik, hogy minden kifejezésnek pontosan
egy normálformája van.

## Korábbi formalizálások hátrányai

* Big-step normalization (Altenkirch & Chapman [@altenkirch2009big]): nem
  standard szintaxis (explicit szubsztitúció), nem teljes formalizálás.

* Catarina Coquand [@coquand2002formalised]: explicit szubsztitúció, formalizálás
  legacy rendszerben (ALF).

* Hereditary substitution (Altenkirch & Keller [@keller2010normalization]): nem
  hatékony algoritmus, bonyolult formalizálás.

## Sorok száma (nagyjából)

Formalizáció                                                              Sorok
------------------------------------------------------------------------  ------
NbE (Kovács)                                                              600
Big-step (Romanenko [@romanenko-bigstep])                                 1600
Hereditary substitution (Altenkirch & Keller [@keller2010normalization])  1200
NbE (Catarina Coquand [@coquand2002formalised])                           ?

## Szintaxis

Függvények (`A ⇒ B`) és egy üres alaptípus (`ι`).\
\
De Bruijn indexek.\
\
Kizárólag jól típusozott termekkel foglalkozunk.\
\
A helyettesítés rekurzív függvény, a $\beta\eta$-konverzió pedig induktív reláció a szintaxison.

## Formális szintaxis

~~~{.agda}
data Ty : Set where
  ι   : Ty
  _⇒_ : Ty → Ty → Ty

data Con : Set where
  ∙   : Con
  _,_ : Con → Ty → Con

data _∈_ (A : Ty) : Con → Set where
  vz : A ∈ (Γ , A)
  vs : A ∈ Γ → A ∈ (Γ , B)

data Tm (Γ : Con) : Ty → Set where
  var : A ∈ Γ → Tm Γ A
  lam : Tm (Γ , A) B → Tm Γ (A ⇒ B)
  app : Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B
~~~


## Formalizálás elvei

A helyettesítések és változó-átnevezések formalizálása vesződséges, könnyű benne
elveszni.\
\

. . .

A részletekbe bonyolódás helyett kiválasztunk egy olyan absztrakciós szintet, ami:

. . .

> (#) Elég absztrakt és világos ahhoz, hogy könnyű legyen áttekinteni.
> (#) Viszont nem *túl absztrakt* olyan értelemben, hogy még egyszerűen leírható Agda-ban.

## Lépések

> (#) Megmutatjuk, hogy a szintaxis a $\beta\eta$-konverzióval és a párhuzamos helyetessítésekkel együtt sCwF (simply typed category with families) algebrai struktúrát alkot.
> (#) Megadjuk az így kapott sCwF presheaf modelljét, ahol a bázis a típuskörnyezetek és a változó-átnevezések kategóriája. Ez megadja a kiértékelés algoritmusát.
> (#) Bevezetünk egy logikai relációt a szintaxis és a presheaf modell között, aminek az alaplemmája megadja a "completeness" tulajdonságot.
> (#) A "soundness" és "stability" egyszerű indukcióval bizonyítható a szintaxis fölött.

## Tanulságok, összefüggések

Erre az egyszerű nyelvre is meglepően bonyolult a normalizálás helyességbizonyítása.\
\

. . .

A bizonyítás elég absztrakt, de megéri.\
\

. . .

Szoros összefüggés logika és programozás között. Az STLC konstruktív
propozícionális logika, az STLC algoritmusai megfelelnek bizonyos logikai
tulajdonságok bizonyításának.\
\

. . .

szemantika    algoritmus                     logika
----------    ---------------------------    --------------------
standard      jól típusozott interpreter     konzisztencia
Kripke        normalizálás                   teljesség
presheaf      normalizálás + helyesség       teljesség/függetlenség

## Kérdések, további munka

> * További egyszerűsítés automatikus bizonyítással segítségével. Létező
>   könyvtárak Agda-ban és máshol.
> * Új alaptípusok bevezetése.
>     + Szorzat és összeg típusok, algebrai típusok.
> * Polimorf és függő típusú nyelvek normalizálása: a jelenlegi módszer sajnos *nem
>   elég absztrakt* ehhez.
>     + A megfelelő absztrakciós szintet nem támogatják jelenlegi bizonyítórendszerek.
>     + Jelenlegi kutatási téma ezeknek az absztrakciós eszközöknek az elmélete
>       és implementációja.

----------
