(module ()
  (ind PGame () (u)
    (sort (univsucc (univsucc (univvar u))))
    0 (
    (PGame.mk
      (pi A ex (sort (univsucc (univvar u)))
        (pi B ex (sort (univsucc (univvar u)))
          (pi left ex
            (pi a ex (bound 1) (inst (complicated_recursors PGame) ((univvar u))))
            (pi right ex
              (pi b ex (bound 1) (inst (complicated_recursors PGame) ((univvar u))))
              (inst (complicated_recursors PGame) ((univvar u)))
            )))))
  ))
  (ind W () (u v)
    (pi A ex (sort (univsucc (univvar u)))
      (pi B ex (pi a ex (bound 0) (sort (univsucc (univvar v))))
        (sort (univmax (univsucc (univvar u)) (univsucc (univvar v))))))
    2 (
    (W.mk
      (pi A ex (sort (univsucc (univvar u)))
        (pi B ex (pi a ex (bound 0) (sort (univsucc (univvar v))))
          (pi a ex (bound 1)
            (pi b ex (pi c ex
              (ap (bound 1) (bound 0))
              (ap (ap (inst (complicated_recursors W) ((univvar u) (univvar v)))
                (bound 3))
                (bound 2)))
              (ap (ap (inst (complicated_recursors W) ((univvar u) (univvar v)))
                (bound 3))
                (bound 2)))
            ))))
  ))
)
