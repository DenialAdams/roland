(import "wasi_unstable" "fd_write" 
(func $fd_write (param i32) (param i32) (param i32) (param i32) (result i32)
)
)
(memory 1)
(export "memory" (memory 0))
(export "_start" (func $main))
(data 0 (i32.const 0) "\n")
(data 0 (i32.const 1) "true")
(data 0 (i32.const 5) "false")
(global $sp (mut i32) (i32.const 16))
(global $bp (mut i32) (i32.const 16))
(global $mem_address (mut i32) (i32.const 0))
(func $wasm_memory_size (result i32)
  memory.size
)
(func $wasm_memory_grow (param i32) (result i32)
  local.get 0
  memory.grow
)
(func $sqrt (param f64) (result f64)
  local.get 0
  f64.sqrt
)
(func $sqrt_f32 (param f32) (result f32)
  local.get 0
  f32.sqrt
)
(func $unreachable 
  unreachable
)
(func $::struct::String::pointer (param i32) (param i32) (result i32)
  local.get 0
)
(func $::struct::String::length (param i32) (param i32) (result i32)
  local.get 1
)
(func $main 
)
(func $print (param i32) (param i32) 
  global.get $sp
  global.get $bp
  i32.store
  global.get $sp
  global.set $bp
  global.get $sp
  i32.const 40
  i32.add
  global.set $sp
  global.get $bp
  i32.const 4
  i32.add
  global.set $mem_address
  global.get $mem_address
  local.get 0
  i32.store
  global.get $mem_address
  i32.const 4
  i32.add
  local.get 1
  i32.store
  global.get $bp
  i32.const 12
  i32.add
  global.get $bp
  i32.const 4
  i32.add
  i32.load
  global.get $bp
  i32.const 4
  i32.add
  i32.const 4
  i32.add
  i32.load
  i32.const 0
  i32.const 1
  call $::struct::String::pointer
  i32.const 0
  i32.const 1
  call $::struct::String::length
  call $::store::0
  global.get $bp
  i32.const 28
  i32.add
  i32.const 0
  i32.store
  block $b_0
    loop $l_0
      block $bi_0
        i32.const 1
        global.get $bp
        i32.const 12
        i32.add
        i32.const 2
        global.get $bp
        i32.const 28
        i32.add
        call $fd_write
        drop
        global.get $bp
        i32.const 32
        i32.add
        global.get $bp
        i32.const 12
        i32.add
        i32.const 4
        i32.add
        i32.store
        global.get $bp
        i32.const 28
        i32.add
        i32.load
        global.get $bp
        i32.const 32
        i32.add
        i32.load
        i32.load
        i32.gt_u
        (if 
          (then 
            br $b_0
          )
          (else 
            global.get $bp
            i32.const 12
            i32.add
            global.get $bp
            i32.const 12
            i32.add
            i32.load
            global.get $bp
            i32.const 28
            i32.add
            i32.load
            i32.add
            i32.store
            global.get $bp
            i32.const 32
            i32.add
            i32.load
            global.get $bp
            i32.const 32
            i32.add
            i32.load
            i32.load
            global.get $bp
            i32.const 28
            i32.add
            i32.load
            i32.sub
            i32.store
          )
        )
      end
      br $l_0
    end
  end
  global.get $sp
  i32.const 40
  i32.sub
  global.set $sp
  global.get $sp
  i32.load
  global.set $bp
)
(func $print_bool (param i32) 
  global.get $sp
  global.get $bp
  i32.store
  global.get $sp
  global.set $bp
  global.get $sp
  i32.const 8
  i32.add
  global.set $sp
  global.get $bp
  i32.const 4
  i32.add
  local.get 0
  i32.store8
  global.get $bp
  i32.const 4
  i32.add
  i32.load8_u
  (if 
    (then 
      i32.const 1
      i32.const 4
      call $print
    )
    (else 
      i32.const 5
      i32.const 5
      call $print
    )
  )
  global.get $sp
  i32.const 8
  i32.sub
  global.set $sp
  global.get $sp
  i32.load
  global.set $bp
)
(func $count_digits (param i64) (result i32)
  global.get $sp
  global.get $bp
  i32.store
  global.get $sp
  global.set $bp
  global.get $sp
  i32.const 24
  i32.add
  global.set $sp
  global.get $bp
  i32.const 8
  i32.add
  local.get 0
  i64.store
  global.get $bp
  i32.const 16
  i32.add
  i32.const 0
  i32.store8
  block $b_0
    loop $l_0
      block $bi_0
        global.get $bp
        i32.const 8
        i32.add
        i64.load
        i64.const 9
        i64.le_u
        (if 
          (then 
            global.get $bp
            i32.const 16
            i32.add
            i32.load8_u
            i32.const 1
            i32.add
            global.get $sp
            i32.const 24
            i32.sub
            global.set $sp
            global.get $sp
            i32.load
            global.set $bp
            return
          )
          (else 
          )
        )
        global.get $bp
        i32.const 16
        i32.add
        global.get $bp
        i32.const 16
        i32.add
        i32.load8_u
        i32.const 1
        i32.add
        i32.store8
        global.get $bp
        i32.const 8
        i32.add
        global.get $bp
        i32.const 8
        i32.add
        i64.load
        i64.const 10
        i64.div_u
        i64.store
      end
      br $l_0
    end
  end
  i32.const 0
  global.get $sp
  i32.const 24
  i32.sub
  global.set $sp
  global.get $sp
  i32.load
  global.set $bp
  return
)
(func $int_to_string (param i64) (result i32) (result i32)
  global.get $sp
  global.get $bp
  i32.store
  global.get $sp
  global.set $bp
  global.get $sp
  i32.const 48
  i32.add
  global.set $sp
  global.get $bp
  i32.const 8
  i32.add
  local.get 0
  i64.store
  global.get $bp
  i32.const 40
  i32.add
  global.get $bp
  i32.const 8
  i32.add
  i64.load
  call $count_digits
  i32.store8
  global.get $bp
  i32.const 16
  i32.add
  global.get $bp
  i32.const 40
  i32.add
  i32.load8_u
  i32.const 1
  i32.sub
  i32.store
  global.get $bp
  i32.const 20
  i32.add
  global.get $bp
  i32.const 40
  i32.add
  i32.load8_u
  call $malloc
  i32.store
  global.get $bp
  i32.const 41
  i32.add
  i32.const 0
  i32.store8
  global.get $bp
  i32.const 24
  i32.add
  i32.const 0
  i32.store
  block $b_0
    loop $l_0
      block $bi_0
        global.get $bp
        i32.const 8
        i32.add
        i64.load
        i64.const 9
        i64.le_u
        (if 
          (then 
            global.get $bp
            i32.const 41
            i32.add
            global.get $bp
            i32.const 8
            i32.add
            i64.load
            i32.wrap_i64
            i32.store8
            global.get $bp
            i32.const 28
            i32.add
            global.get $bp
            i32.const 20
            i32.add
            i32.load
            global.get $bp
            i32.const 16
            i32.add
            i32.load
            i32.add
            global.get $bp
            i32.const 24
            i32.add
            i32.load
            i32.sub
            i32.store
            global.get $bp
            i32.const 28
            i32.add
            i32.load
            global.get $bp
            i32.const 41
            i32.add
            i32.load8_u
            i32.const 48
            i32.add
            i32.store8
            global.get $bp
            i32.const 24
            i32.add
            global.get $bp
            i32.const 24
            i32.add
            i32.load
            i32.const 1
            i32.add
            i32.store
            br $b_0
          )
          (else 
          )
        )
        global.get $bp
        i32.const 41
        i32.add
        global.get $bp
        i32.const 8
        i32.add
        i64.load
        i64.const 10
        i64.rem_u
        i32.wrap_i64
        i32.store8
        global.get $bp
        i32.const 8
        i32.add
        global.get $bp
        i32.const 8
        i32.add
        i64.load
        i64.const 10
        i64.div_u
        i64.store
        global.get $bp
        i32.const 28
        i32.add
        global.get $bp
        i32.const 20
        i32.add
        i32.load
        global.get $bp
        i32.const 16
        i32.add
        i32.load
        i32.add
        global.get $bp
        i32.const 24
        i32.add
        i32.load
        i32.sub
        i32.store
        global.get $bp
        i32.const 28
        i32.add
        i32.load
        global.get $bp
        i32.const 41
        i32.add
        i32.load8_u
        i32.const 48
        i32.add
        i32.store8
        global.get $bp
        i32.const 24
        i32.add
        global.get $bp
        i32.const 24
        i32.add
        i32.load
        i32.const 1
        i32.add
        i32.store
      end
      br $l_0
    end
  end
  global.get $bp
  i32.const 32
  i32.add
  global.get $bp
  i32.const 24
  i32.add
  i32.load
  i32.store
  global.get $bp
  i32.const 36
  i32.add
  global.get $bp
  i32.const 20
  i32.add
  i32.load
  i32.store
  global.get $bp
  i32.const 36
  i32.add
  i32.load
  global.get $bp
  i32.const 32
  i32.add
  i32.load
  global.get $sp
  i32.const 48
  i32.sub
  global.set $sp
  global.get $sp
  i32.load
  global.set $bp
  return
)
(func $malloc (param i32) (result i32)
  global.get $sp
  global.get $bp
  i32.store
  global.get $sp
  global.set $bp
  global.get $sp
  i32.const 16
  i32.add
  global.set $sp
  global.get $bp
  i32.const 4
  i32.add
  local.get 0
  i32.store
  global.get $bp
  i32.const 8
  i32.add
  global.get $bp
  i32.const 4
  i32.add
  i32.load
  i32.const 65536
  i32.div_u
  global.get $bp
  i32.const 4
  i32.add
  i32.load
  i32.const 65536
  i32.rem_u
  i32.const 0
  i32.ne
  i32.add
  i32.store
  global.get $bp
  i32.const 12
  i32.add
  global.get $bp
  i32.const 8
  i32.add
  i32.load
  call $wasm_memory_grow
  i32.const 65536
  i32.mul
  i32.store
  global.get $bp
  i32.const 12
  i32.add
  i32.load
  global.get $sp
  i32.const 16
  i32.sub
  global.set $sp
  global.get $sp
  i32.load
  global.set $bp
  return
)
(func $::store::0 (param i32) (param i32) (param i32) (param i32) (param i32)
  local.get 0
  local.get 1
  i32.store
  local.get 0
  i32.const 4
  i32.add
  local.get 2
  i32.store
  local.get 0
  i32.const 8
  i32.add
  local.get 3
  i32.store
  local.get 0
  i32.const 12
  i32.add
  local.get 4
  i32.store
)
