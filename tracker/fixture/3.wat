(module
 (import "env" "memory" (memory $mimport$0 512))
 (func $19661 (param $0 i32) (param $1 i32) (result i32) (i32.const 0))
 (func $17422 (param $0 i32) (param $1 i32) (result i32) (i32.const 1))
 (func $15177 (param $0 i32) (param $1 i32) (param $2 i32) (result i32) (i32.const 2))
 (func $19672 (param $0 i32) (param $1 i32) (result i32) (i32.const 3))
 (func $17426 (param $0 i32) (param $1 i32) (result i32) (i32.const 4))
 (func $12386 (param $0 i32) (param $1 i32) (param $2 i32) (result i32) (i32.const 5))
 (func $19685 (param $0 i32) (param $1 i32) (result i32) (i32.const 6))
 (func $17452 (param $0 i32) (param $1 i32) (result i32) (i32.const 7))
 (func $18797 (param $0 i32) (param $1 i32) (param $2 i32) (result i32) (i32.const 8))

 (func $wasm_shrink_target_primary (param $0 i32) (param $1 i32) (param $2 i32) (param $3 i32)
  (local $4 i32)
  (local $5 i32)
  (local $6 i32)
  (local $7 i32)
  (local $8 i32)
  (local $9 i32)
  (local $10 i32)
  (local $11 i32)
  (local.set $6
   (i32.add
    (local.get $1)
    (i32.const 1)
   )
  )
  (local.set $7
   (i32.add
    (local.get $1)
    (i32.const 28)
   )
  )
  (local.set $5
   (i32.const -1)
  )
  (local.set $4
   (i32.and
    (local.tee $8
     (i32.add
      (i32.load offset=32
       (local.get $1)
      )
      (i32.const -1)
     )
    )
    (local.get $3)
   )
  )
  (block $label$1
   (block $label$2
    (block $label$3
     (loop $label$4
      (br_if $label$3
       (call $19661
        (local.get $1)
        (local.get $4)
       )
      )
      (local.set $5
       (block (result i32)
        (local.set $11
         (if (result i32)
          (call $17422
           (local.get $1)
           (local.get $4)
          )
          (if (result i32)
           (i32.eq
            (local.get $5)
            (i32.const -1)
           )
           (local.get $4)
           (local.get $5)
          )
          (block (result i32)
           (br_if $label$2
            (call $15177
             (local.get $6)
             (local.get $2)
             (i32.add
              (i32.load
               (local.get $7)
              )
              (i32.shl
               (local.get $4)
               (i32.const 3)
              )
             )
            )
           )
           (local.get $5)
          )
         )
        )
        (local.set $9
         (local.tee $10
          (i32.add
           (local.get $9)
           (i32.const 1)
          )
         )
        )
        (local.get $11)
       )
      )
      (local.set $4
       (i32.and
        (i32.add
         (local.get $10)
         (local.get $4)
        )
        (local.get $8)
       )
      )
      (br $label$4)
     )
    )
    (i32.store
     (local.get $0)
     (i32.const -1)
    )
    (local.set $0
     (i32.add
      (local.get $0)
      (i32.const 4)
     )
    )
    (if
     (i32.eq
      (local.get $5)
      (i32.const -1)
     )
     (i32.store
      (local.get $0)
      (local.get $4)
     )
     (i32.store
      (local.get $0)
      (local.get $5)
     )
    )
    (br $label$1)
   )
   (i32.store
    (local.get $0)
    (local.get $4)
   )
   (i32.store offset=4
    (local.get $0)
    (i32.const -1)
   )
  )
 )
 (func $wasm_shrink_target_func_0 (param $0 i32) (param $1 i32) (param $2 i32) (param $3 i32)
  (local $4 i32)
  (local $5 i32)
  (local $6 i32)
  (local $7 i32)
  (local $8 i32)
  (local $9 i32)
  (local $10 i32)
  (local $11 i32)
  (local.set $6
   (i32.add
    (local.get $1)
    (i32.const 1)
   )
  )
  (local.set $7
   (i32.add
    (local.get $1)
    (i32.const 28)
   )
  )
  (local.set $5
   (i32.const -1)
  )
  (local.set $4
   (i32.and
    (local.tee $8
     (i32.add
      (i32.load offset=32
       (local.get $1)
      )
      (i32.const -1)
     )
    )
    (local.get $3)
   )
  )
  (block $label$1
   (block $label$2
    (block $label$3
     (loop $label$4
      (br_if $label$3
       (call $19672
        (local.get $1)
        (local.get $4)
       )
      )
      (local.set $5
       (block (result i32)
        (local.set $11
         (if (result i32)
          (call $17426
           (local.get $1)
           (local.get $4)
          )
          (if (result i32)
           (i32.eq
            (local.get $5)
            (i32.const -1)
           )
           (local.get $4)
           (local.get $5)
          )
          (block (result i32)
           (br_if $label$2
            (call $12386
             (local.get $6)
             (local.get $2)
             (i32.add
              (i32.load
               (local.get $7)
              )
              (i32.shl
               (local.get $4)
               (i32.const 3)
              )
             )
            )
           )
           (local.get $5)
          )
         )
        )
        (local.set $9
         (local.tee $10
          (i32.add
           (local.get $9)
           (i32.const 1)
          )
         )
        )
        (local.get $11)
       )
      )
      (local.set $4
       (i32.and
        (i32.add
         (local.get $10)
         (local.get $4)
        )
        (local.get $8)
       )
      )
      (br $label$4)
     )
    )
    (i32.store
     (local.get $0)
     (i32.const -1)
    )
    (local.set $0
     (i32.add
      (local.get $0)
      (i32.const 4)
     )
    )
    (if
     (i32.eq
      (local.get $5)
      (i32.const -1)
     )
     (i32.store
      (local.get $0)
      (local.get $4)
     )
     (i32.store
      (local.get $0)
      (local.get $5)
     )
    )
    (br $label$1)
   )
   (i32.store
    (local.get $0)
    (local.get $4)
   )
   (i32.store offset=4
    (local.get $0)
    (i32.const -1)
   )
  )
 )
 (func $wasm_shrink_target_func_1 (param $0 i32) (param $1 i32) (param $2 i32) (param $3 i32)
  (local $4 i32)
  (local $5 i32)
  (local $6 i32)
  (local $7 i32)
  (local $8 i32)
  (local $9 i32)
  (local $10 i32)
  (local $11 i32)
  (local.set $6
   (i32.add
    (local.get $1)
    (i32.const 1)
   )
  )
  (local.set $7
   (i32.add
    (local.get $1)
    (i32.const 28)
   )
  )
  (local.set $5
   (i32.const -1)
  )
  (local.set $4
   (i32.and
    (local.tee $8
     (i32.add
      (i32.load offset=32
       (local.get $1)
      )
      (i32.const -1)
     )
    )
    (local.get $3)
   )
  )
  (block $label$1
   (block $label$2
    (block $label$3
     (loop $label$4
      (br_if $label$3
       (call $19685
        (local.get $1)
        (local.get $4)
       )
      )
      (local.set $5
       (block (result i32)
        (local.set $11
         (if (result i32)
          (call $17452
           (local.get $1)
           (local.get $4)
          )
          (if (result i32)
           (i32.eq
            (local.get $5)
            (i32.const -1)
           )
           (local.get $4)
           (local.get $5)
          )
          (block (result i32)
           (br_if $label$2
            (call $18797
             (local.get $6)
             (local.get $2)
             (i32.add
              (i32.load
               (local.get $7)
              )
              (i32.shl
               (local.get $4)
               (i32.const 3)
              )
             )
            )
           )
           (local.get $5)
          )
         )
        )
        (local.set $9
         (local.tee $10
          (i32.add
           (local.get $9)
           (i32.const 1)
          )
         )
        )
        (local.get $11)
       )
      )
      (local.set $4
       (i32.and
        (i32.add
         (local.get $10)
         (local.get $4)
        )
        (local.get $8)
       )
      )
      (br $label$4)
     )
    )
    (i32.store
     (local.get $0)
     (i32.const -1)
    )
    (local.set $0
     (i32.add
      (local.get $0)
      (i32.const 4)
     )
    )
    (if
     (i32.eq
      (local.get $5)
      (i32.const -1)
     )
     (i32.store
      (local.get $0)
      (local.get $4)
     )
     (i32.store
      (local.get $0)
      (local.get $5)
     )
    )
    (br $label$1)
   )
   (i32.store
    (local.get $0)
    (local.get $4)
   )
   (i32.store offset=4
    (local.get $0)
    (i32.const -1)
   )
  )
 )
)
