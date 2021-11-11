(module
  (import "env" "STACKTOP" (global $gimport$2 i32))
  (table (;0;) 12755 12755 funcref)
  (global (;7;) (mut i32) (i32.const 2))
  (memory (;0;) 31)
  (global $global$1 (mut i32) (global.get $gimport$2))
  (func $wasm_shrink_debug_target_to (param $0 i32)
  (if
   (i32.const 0)
   (block
    (loop $label$6
     (drop (i32.const 28))
    )
   )
   (block
   )
  )
 )

  (func $wasm_shrink_debug_target_from (param $0 i32)
  (if
   (i32.const 0)
   (block
    (loop $label$6
     (drop (i32.const 48))
    )
   )
   (block
   )
  )
 )
)
