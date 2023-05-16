# TODO

## Model, Traces...

- On ne gère pas les variables de dimension quelconques....

## Simulateur

- La trace devrait garder le nb_proc
- On voudrait avoir une fonction Take_transition_if_possible qui essaye de prendre une transition avec arguments quelconque si possible

## Compilateur

- La plupart du code entre l'écriture des garde et des états unsafe semble aisément factorisable
- Pourquoi utiliser des StringMap non persistant plutôt que juste des hashtbl string, unit ?

## Compilation / Makefile

- Donner la possibilté de save le mymodel.ml ?
