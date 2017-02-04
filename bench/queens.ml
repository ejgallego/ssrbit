let output = open_out "queens_ml.dat"

let solutions =
  (* counting from 1 *)
  [| 1 ; 0 ; 0 ; 2 ; 10 ; 4 ; 40 ; 92 ; 352 ; 724 ; 
     2680 ; 14200 ; 73712 ; 365596 ; 2279184 ; 14772512 ;
     95815104 ; 666090624 ; 4968057848 ; 39029188884 ; 
     314666222712 ; 2691008701644 ; 24233937684440 |]

let rec t cols asc_diag desc_diag =
  if cols = 0 then 1 
  else
    let valid = cols land (lnot (asc_diag lor desc_diag)) in
    let rec loop valid score = 
      if valid <> 0 then
        let col = valid land (- valid) in
        loop (valid land (lnot col))
             (score + (t (cols land (lnot col)) 
                         ((asc_diag lor col) lsr 1) ((desc_diag lor col) lsl 1)))
      else
          score
    in
    loop valid 0

let nqueens n =
  t (1 lsl n - 1) 0 0

let _ = 
  for i = 1 to 15 do
    let time = Unix.gettimeofday() in
    let solution = nqueens i in
    let time = Unix.gettimeofday() -. time in
    Printf.printf "%d queens: %f s.\n%!" i time;
    Printf.fprintf output "%d\t%f\n" i time;
    assert (solutions.(i-1) = solution)
  done
