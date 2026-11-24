import YM.QCD.Bay.Lotus
import YM.Next.FREE_KERNELS.Traffic
import YM.Extra.ITERATION_NO_LOSS.Geometry
/-! # Root read of straight actual fine field. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Port
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Leaf Tee Flume Orbit Quarry Stationary Fork Pine YM.Next.Free Push.Local
open Jets Sun Revolve Garden Bay Strut LeafM Paths Relation Corona
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c f:Side}(r: Ratio c f) {v η A :ℝ} {B b:ℕ}

def lowC (U:Grid f): Grid c:=fun i=> travel U (r.embed i.1) (List.replicate r.count.val (posDir i.2))
lemma axisC (U:Grid f) (x:Site c)(a:Step) : a.read (lowC r U) x=travel U (r.embed x) (List.replicate r.count.val a):=by
   rcases a with ⟨i,_|_⟩; · rfl
   let d:=posDir i; let y:= x-step i; have he:y+d.vec=x:=by simp [y,d]
   rw [show List.replicate r.count.val ⟨i,true⟩=Lattice.reverse (List.replicate r.count.val d) from by simp [d,Lattice.reverse,negDir], show r.embed x=stop (r.embed y) (List.replicate r.count.val d) from by rw [Revolve.cone,he], travel_reverse]; rfl
lemma pulled (u: Strut c) (U:Grid f): lowC r (sky (raise r u) U)=sky u (lowC r U):=by
   funext i; unfold lowC sky raise; simp only [travel_pull,List.map_replicate]; change travel _ _ _=((posDir i.2).rotate u.1).read (lowC r U) _
   rw [axisC]; congr 2; unfold affine; rw [← r.signed]; exact (r.root.map_add ..).symm
lemma framed_c (p:Frame f) (U : Grid f): lowC r (gauge p U)=gauge (p ∘ r.embed) (lowC r U):=by
   funext i; unfold lowC; rw [travel_gauge,Revolve.cone]; rfl
lemma former : lowC r 1=1:=by
   have he x (w:Walk):travel (1:Grid f) x w=1:=by
     induction w generalizing x with
     | nil=>rfl
     | cons a w ih=> rcases a with ⟨i,n|n⟩ <;> simp [travel,Step.read,ih]
   funext i; exact he ..

def rig (X: Support c): Support f := halo r.count.val (X.image r.embed)
lemma firm {U V: Grid f}{X : Support c} (H : Agrees (rig r X) U V):Agrees X (lowC r U) (lowC r V):=by
  intro i h1 h2; apply travel_local _ _ U V (agrees_mono H ?_); intro a ha; refine halo_spec.mpr ⟨_,mem_image_of_mem r.embed h1,?_⟩; simpa only [List.length_replicate] using Extra.Iteration.Shapes.visits_dist _ _ _ ha
lemma coversB (W: Support c)(h:r.count.val*(b+1) ≤ B): coverNumber B (rig r W) ≤ coverNumber b W:=by
   obtain ⟨D,⟨hv,H⟩,he⟩:= coverNumber_realized b W
   let Y:= D.image r.embed
   have hh : Ships Y (B+B+1):= by
     intro i hi j hj; obtain ⟨x,hx,rfl⟩:= mem_image.mp hi; obtain ⟨y,hy,rfl⟩:=mem_image.mp hj
     have hh : ReflTransGen (Touch D (b+b+1)) x y:= halo_ship b H _ hx _ hy
     induction hh with
     | refl=> exact .refl
     | tail ih hx hh=> exact .tail (hh hx.1 (mem_image_of_mem _ hx.1)) ⟨mem_image_of_mem _ hx.1,mem_image_of_mem _ hx.2.1,by refine (YM.Next.Free.scaled_root r _ _).trans ((Nat.mul_le_mul_left _ hx.2.2).trans ?_); simp only [Nat.mul_add,Nat.mul_one] at *; omega⟩
   have hp : covers B (rig r W) Y:=by
     refine ⟨fun i hi=> ?_,ship_halo _ hh⟩
     obtain ⟨a,hP,hz⟩:= halo_spec.mp hi; obtain ⟨x,hx,rfl⟩:= mem_image.mp hP; obtain ⟨z,Z,hm⟩:= halo_spec.mp (hv hx)
     exact halo_spec.mpr ⟨_,mem_image_of_mem _ Z,(separation_triangle _ _ _).trans ((Nat.add_le_add ((YM.Next.Free.scaled_root r z x).trans (Nat.mul_le_mul_left _ hm)) hz).trans (by rw [← Nat.mul_succ]; exact h))⟩
   apply Nat.le_trans (m:=Y.card) (Nat.find_min' _ ⟨Y,hp,rfl⟩); exact Finset.card_image_le.trans_eq he

def warp (X:Pulse f):Pulse c:= (fun i=> pursueP X (r.embed i.1) (List.replicate r.count.val (posDir i.2)),fun i=>pursueP X (r.embed (i.1+step i.2)) (List.replicate r.count.val (negDir i.2)))
lemma posedW (U:Grid f): warp r (settled U)=settled (lowC r U):=by
    apply Prod.ext; · exact funext fun i=> pursuit ..
    funext i; change pursueP (settled U) _ _=star (_); rw [pursuit,← axisC]; simp [colour_inv]
lemma warping : Differentiable ℂ (warp r):= (differentiable_pi.mpr (fun i : Edge (Site c)=> reachP (r.embed i.1) (List.replicate r.count.val (posDir i.2)))).prodMk (differentiable_pi.mpr (fun i : Edge (Site c)=> reachP _ _))
lemma turnout {x:Pulse f}(hx:x∈Kingdom f v)(hu:v≤1)(ht:(3:ℝ)^r.count.val*v ≤ η) : warp r x∈ Kingdom c η := by
   obtain ⟨U,hU⟩:=Set.mem_iUnion.mp hx; rw [Metric.mem_ball, dist_eq_norm] at hU
   have hv : x∈ Metric.ball (settled U) ((2:ℝ)/2):=by rw [Metric.mem_ball,dist_eq_norm]; exact hU.trans_le (hu.trans_eq (by norm_num))
   let Z := (3:ℝ)^r.count.val; have hz:0<Z:=pow_pos (by norm_num) _
   have h i w(h:List.length w=r.count.val): ‖pursueP x i w-pursueP (settled U) i w‖ ≤ Z*‖x-settled U‖:=by
     have he:=lastwig (fun s=>pursueP s i w) (show (0:ℝ)<2 by norm_num) (fun y _=> reachP i w y) (R:=Z) (fun y hy=>?_) hv; swap
     · rw [Metric.mem_ball,dist_eq_norm] at hy; exact (pose y U w i hy.le).trans_eq (by rw [h]; norm_num [Z]) -- adjust
     simpa using he
   refine Set.mem_iUnion.mpr ⟨lowC r U,?_⟩; rw [Metric.mem_ball,← posedW,dist_eq_norm]; apply lt_of_le_of_lt ?_ ((mul_lt_mul_of_pos_left hU hz).trans_le ht); unfold warp; rw [Prod.norm_def]; apply max_le <;> (apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr; intro i; exact h _ _ (List.length_replicate ..))
end YM.QCD.Port
