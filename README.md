��#   A u g m e n t e d - S h a l l o w - E m b e d d i n g s  
 #   A u g m e n t e d - S h a l l o w - E m b e d d i n g s  
 
See: https://agda.readthedocs.io/en/v2.6.2/tools/generating-latex.html
run ```agda --latex {file}.lagda``` to convert lagda into latex

#

Each file has a "-paper" version which has implicit arguments removed.

This can be run with ```agda --latex --only-scope-checking {file}.lagda```.

The idea is that these files don't actually typecheck, but look nicer.
