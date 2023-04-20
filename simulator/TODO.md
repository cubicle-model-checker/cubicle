# TODO

## Général

Devrait-on passer sur dune pour un modèle de compilation plus efficace ?
Devrait-on même garder le même répertoire git pour le simulateur que pour cubicle ?

## Model

- Utiliser une structure de donnée non persistante

## Simulateur

- La trace devrait garder le nb_proc
- Pour avoir un simulateur qui lit une trace : 
		Set la trace
		Set modèle vide
		Se balader dans la trace
- Un appel a step si il existe des états après la ou on est devrait retourner vers ces états. Une fonction tierce "forget future" devrait exister pour supprimer les traces futures.

## Traces

Implémenter la fonction "save trace", qui est une fonction avec la même signature que le modèle 
(de façon a pouvoir être lu par les mêmes programme)
Mais qui n'itère que sur un modèle.

## Compilateur

- Il faudrait un paramètre -o pour spécifier le path
- Mettre le "max_float" dans Simulator.Utils plutôt que dans le cutils
- La plupart du code entre l'écriture des garde et des états unsafe semble aisément factorisable
- Mettre un message dans la console pour dire que la compilation s'est bien passé et ou retrouver le fichier

## Scenes 

- Refresh l'écran lors d'une mise en pause pour afficher le texte
- Vérifier état unsafe 
- Afficher numéro du step courant quelque part

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

Composition.ml : Grid_composition

Mettre beaucoup de commentaire dans les examples (notament ascenceur)

## TESTER PETRI

- Hierarchical snoop

## NOTES : 

Quand on met un tiret dans le nom d'une variable, l'ast retire le tirer apparament

## BUGS : /!\

init(p) {

	proc[p] = p ne marche pas car considère p comme un vconstr

}
