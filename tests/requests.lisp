;; Sample requests for the stateless service:  bin/mccarthy serve < tests/requests.lisp
(prove :sig ((p bool) (q bool)) :goal (==> (and p q) (and q p)))
(prove :sig ((p bool) (q bool) (r bool))
       :goal (==> (==> p q) (==> (==> q r) (==> p r))))
(prove :sig ((p (fun a bool)) (c a)) :goal (==> (! (x a) (p x)) (p c)))
(learn :sig ((p bool) (q bool)) :goal (==> p (==> q (and p q))))
(facts)
(prove :sig ((p (fun a bool)) (c a)) :goal (==> (p c) (! (x a) (p x))))  ; non-theorem
(quit)
