# Introduction

HarmTrace (Harmony Analysis and Retrieval of Music with Type-level 
Representations of Abstract Chords Entities) is a system for automatic harmony 
analysis of music. It takes a sequence of chords as input and produces a harmony 
analysis, which can be visualised as a tree. 


Music theory has been essential in composing and performing music for centuries. 
Within Western tonal music, from the early Baroque on to modern-day jazz and pop 
music, the function of chords within a chord sequence can be explained by 
harmony theory. Although Western tonal harmony theory is a thoroughly studied 
area, formalising this theory is a hard problem. 


With HarmTrace we have developed a formalisation of the rules of tonal harmony 
as a Haskell (generalized) algebraic datatype. Given a sequence of chord labels, 
the harmonic function of a chord in its tonal context is automatically derived. 
For this, we use several advanced functional programming techniques, such as 
type-level computations, datatype-generic programming, and error-correcting 
parsers. Our functional model of harmony offers various benefits: it can be used 
to define harmonic similarity measures and facilitate music retrieval, or it can 
help musicologists in batch-analysing large corpora of digitised scores, for 
instance. 


HarmTrace is covered in depth in the following papers: 

de Haas, W. B., et al. "Automatic Functional Harmonic Analysis." 
_[Computer Music Journal](http://www.mitpressjournals.org/doi/10.1162/COMJ_a_00209)_ 
37.4 (2013): 37-53. 
([PDF](http://www.mitpressjournals.org/doi/pdf/10.1162/COMJ_a_00209))

Magalhaes, J. P., & de Haas, W. B. (2011, September). Functional modelling of
musical harmony: an experience report. In 
_[ACM SIGPLAN Notices](http://dl.acm.org/citation.cfm?id=2034797&dl=ACM&coll=DL&CFID=792765209&CFTOKEN=90344854)_ 
(Vol. 46, No. 9, pp. 156-162). ACM. 
([PDF](http://www.cs.uu.nl/groups/MG/multimedia/publications/art/icfp2011.pdf))

# Installation

This fork has been modified to compile with GHC 9.4.8 using Cabal. The original version was compatible with GHC 7.10 and used Stack.

The main changes are:

*   Code adjustments to be compatible with GHC 9.4.8 and newer versions of dependencies like `hmatrix` and `Diff`.
*   The `HarmTrace-Base` dependency has been integrated directly into the `src/` directory.
*   The `instant-generics` dependency has been included as a local copy in the `instant-generics/` directory. This is necessary for compilation and points to a modified version of the library also available at `https://github.com/superguaricho/instant-generics`.

To build the project, you can use `cabal`:

```
cabal build
```

# Running HarmTrace

You can use Cabal to run HarmTrace. Note the `--` separator which is needed to pass arguments to the executable itself.

```
>>> cabal run harmtrace -- --help
harmtrace [COMMAND] ... [OPTIONS]
  Harmonic Analysis and Retrieval of Music

Commands:
  parse      Parse files into harmonic analysis trees
  match      Harmonic similarity matching
  recognise  Recognise chords from audio files

  -r=file            File to read flags from
  -?      --help     Display help message
  -V      --version  Print version information
```

All modes have separate help pages:
```
>>> cabal run harmtrace -- parse --help
parse [OPTIONS]
  Parse files into harmonic analysis trees

  -g      --grammar=string    Grammar to use (jazz|pop)
  -c      --chords=string     Input chord sequence to parse
  -i      --file=filepath     Input file to parse
  -d      --dir=filepath      Input directory to parse all files within
  -o      --out=filepath      Output binary file to write parse results to
  -k      --key=filepath      Ground-truth key annotation file
  -x      --key-dir=filepath  Ground-truth key annotation directory
  -p      --print             Output a .png of the parse tree
  -s      --print-insertions  Show inserted nodes
  -r=file                     File to read flags from
  -?      --help              Display help message
  -V      --version           Print version information
```

You can parse a chord sequence with `--chords` the chord should be in [Harte 
syntax](http://ismir2005.ismir.net/proceedings/1080.pdf) suffixed with a 
`;INT` indicating the duration of the chord and separated by spaces. The 
first 'chord' represents a key signature. For instance:
```
>>> cabal run harmtrace -- parse --grammar=jazz --chords="C:maj D:min;1 G:7;2 C:maj;1"
parsed 3 chords into 1 analysis tree(s)
[Piece[PD[D_1_1[S_1par_1[IIm_1[D:min]]][D_2_1[V7_2[G:7]]]]][PT[T_1_1[I_1[C:maj]]]]]
```
If you add `--print`, HarmTrace will render a .PNG image for you using 
[http://ironcreek.net/phpsyntaxtree/](http://ironcreek.net/phpsyntaxtree/)
