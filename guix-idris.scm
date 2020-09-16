(use-modules
	(guix profiles)
	(gnu packages idris)
	(guix packages)
	(guix git-download)
	(guix download)
	(guix build-system gnu)
	((guix licenses) #:prefix license:)
	(gnu packages multiprecision)
	(gnu packages llvm)
	(gnu packages chez))

(define idris2-boot
	(let ((commit "0fb1192cd30ec4747cbc727f26ddbfad515d1363"))
		(package
			(name "idris2-boot")
			(version (git-version "0.1.0" "1" commit))
			(source (origin
				(method git-fetch)
				(uri (git-reference
					(url "git://github.com/edwinb/idris2-boot.git")
					(commit commit)))
				(sha256 (base32 "1f0b2mb7xahc4mrhbw8vp5b6iv3ci1z7yz7h12i8mnmy3nddpsfn"))
				(file-name (git-file-name name version))))
			(build-system gnu-build-system)
			(arguments `(#:phases (modify-phases %standard-phases
				(replace 'configure (lambda _
					(let ((out (assoc-ref %outputs "out")))
						(setenv "PREFIX" out)
						(setenv "IDRIS_CC" "clang"))))
				(replace 'build (lambda _
					(invoke "make" (string-append "PREFIX=" (getenv "PREFIX")) "idris2boot" "libs")))
				(replace 'install (lambda _
					(invoke "make" (string-append "PREFIX=" (getenv "PREFIX")) "install-all")))
				(delete 'check)
				)))
			(inputs `(
				("clang" ,clang)
				("idris" ,idris)
				("gmp" ,gmp)
				("chez-scheme" ,chez-scheme)))
			(home-page "https://idris-lang.org/")
			(synopsis "A dependently typed programming language, a successor to Idris")
			(description "This is the bootstrapping version of Idris 2, the successor to Idris. Its sole purpose is to build Idris 2 proper.")
			(license license:bsd-3))))

(define (make-idris2 version hash boot boot-bin-name)
	(package
		(name "idris2")
		(version version)
		(source (origin
			(method url-fetch)
			(uri (string-append
				"https://github.com/idris-lang/Idris2/archive/v"
				version
				".tar.gz"))
      (sha256 (base32 hash))))
		(build-system gnu-build-system)
		(arguments `(
			#:phases (modify-phases %standard-phases
				(replace 'configure (lambda* (#:key inputs outputs #:allow-other-keys)
					(setenv "PREFIX" (assoc-ref outputs "out"))
					(setenv "CC" "clang")
					#t))
				(delete 'bootstrap)
				(replace 'build (lambda* (#:rest args)
					(invoke "make"
						(string-append "PREFIX=" (getenv "PREFIX"))
						(string-append "IDRIS2_BOOT=" ,boot-bin-name)
						"support" "build/exec/idris2" "testbin")
					(patch-shebang (string-append (getcwd) "/build/exec/idris2"))
					(invoke "make"
						(string-append "PREFIX=" (getenv "PREFIX"))
						(string-append "IDRIS2_BOOT=" ,boot-bin-name)
						"libs")))
				(replace 'install (lambda _
					(invoke "make"
						(string-append "PREFIX=" (getenv "PREFIX"))
						(string-append "IDRIS2_BOOT=" ,boot-bin-name)
						"install")))
				(delete 'check)
				)
			))
		(native-inputs `(
			("idris2-boot" ,boot)
			("clang" ,clang)))
		(inputs `(
			("chez-scheme" ,chez-scheme)))
		(home-page "https://idris-lang.org/")
		(synopsis "A dependently typed programming language, a successor to Idris")
		(description "")
		(license license:bsd-3)))

(define idris2-boot-0.2.1 (make-idris2 "0.2.1" "1izw68vnic9rh5yzvq85f9bm9qnkbdiipfqymgq04a2rr59n5qbv" idris2-boot "idris2boot"))
(define idris2 (make-idris2 "0.2.1" "1izw68vnic9rh5yzvq85f9bm9qnkbdiipfqymgq04a2rr59n5qbv" idris2-boot-0.2.1 "idris2"))

(packages->manifest (list
	idris idris-lens
	idris2))
