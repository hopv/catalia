;; 4 integers
;; v the node value
;; w type of node, either leaf or node
;; x is the left sub-tree sorted so far?
;; y is the right sub-tree sorted so far?
;; z tree height
(
 ( "treeOfInt"
   ( "nodetreeOfInt"
	 ( (v lv lw lx ly lz rv rw rx ry rz)
	   v
	   1
	   (ite
		 (or
		  (= lw 0)
		  (and (<= lv v) (= lx 1) (= ly 1)))
		1
		0)
	   (ite
		 (or
		  (= rw 0)
		  (and (> rv v) (= rx 1) (= ry 1)))
		1
		0)
	   (+ 1 (ite (> lz rz) lz rz))
	   )
	 )
   ( "leaftreeOfInt"
	 ( ()
	   0
	   0
	   1
	   1
	   0
	   )
	 )
   )
 )
