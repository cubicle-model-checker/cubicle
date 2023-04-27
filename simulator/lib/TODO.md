# TODO

## Model

- Utiliser une structure de donnée non persistante

## Simulateur

- La trace devrait garder le nb_proc

## Compilateur

- Mettre le "max_float" dans Simulator.Utils plutôt que dans le cutils
- La plupart du code entre l'écriture des garde et des états unsafe semble aisément factorisable

## Scenes 

Dans un monde idéal : 
- Avoir des flèches qui sont des courbes et plus des droites pour permettre plus de flexibilité
- Ordonner proprement les procs pour qu'on comprenne bien qui est le nouveau proc
- Pouvoir zoomer et dézoomer avec la caméra
- Menu d'aide en appuyant sur h

On devrait pouvoir tuer un proc : 
-> Regarder algo résistants aux pannes 

Pouvoir déplacer transition et état dans l'espace

- Camera speed
- Camera on/off .. With mouse/without...

Petrilib : Utiliser la composition de grille de compositor.ml

Idéallement même une shape dans structure Bouton / Indicateur (Cercle, Rectangle, filled ?)

## Compilation / Makefile

On voudrait utiliser des fichiers temporaires dans la compilation de la scene
Make clean devrait retirer les fichier .cmt et .cmti non ?
