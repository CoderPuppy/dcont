(use-modules
	(guix profiles)
	(gnu packages idris))

(packages->manifest (list
	idris
	idris-lens))
