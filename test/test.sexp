(module
    ()
    (def id (u)
        (lam T imp (sort (univzero))
        (lam x ex (bound 0)
        (bound 0)))
    )
    (ind Bool () () (sort (univsucc (univzero))) (
        (true (inst (Bool) ()))
        (false (inst (Bool) ()))
    ))
)
