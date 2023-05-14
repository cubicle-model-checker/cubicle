# TODO

## Model, Traces...

Gros problème : On ne gère pas les variables de dimension quelconques....

## Simulateur

- La trace devrait garder le nb_proc

## Compilateur

- La plupart du code entre l'écriture des garde et des états unsafe semble aisément factorisable
- Pourquoi utiliser des StringMap non persistant plutôt que juste des hashtbl string, unit ?

## Compilation / Makefile

On voudrait utiliser des fichiers temporaires dans la compilation de la scene
On voudrait silence le ocamlc qui assemble le modèle
On voudrait mieux nettoyer le fichier courant des reste de la compilation
