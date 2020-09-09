(use-modules
	(guix profiles)
	(gnu packages haskell)
	(gnu packages haskell-xyz)
	(guix packages)
	(guix download)
	(guix build-system haskell)
	(guix licenses))

(define ghc-indexed (package
  (name "ghc-indexed")
  (version "0.1.3")
  (source
    (origin
      (method url-fetch)
      (uri (string-append
             "https://hackage.haskell.org/package/indexed/indexed-"
             version
             ".tar.gz"))
      (sha256
        (base32
          "1hpmzg9ziqgng4wh4g0x4p6sdvn9f31hymwxdvfffydzqq70k17g"))))
  (build-system haskell-build-system)
  (home-page
    "http://hackage.haskell.org/package/indexed")
  (synopsis "Haskell98 indexed functors, monads, comonads")
  (description "")
  (license bsd-3)))

(packages->manifest (list
	ghc
	ghc-lens
	ghc-indexed))
