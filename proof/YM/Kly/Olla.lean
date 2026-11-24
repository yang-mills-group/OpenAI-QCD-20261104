import YM.Kly.Cubit
set_option autoImplicit false
set_option maxHeartbeats 610000
noncomputable section
namespace YM.Massive.Bridge.Kly
open Function Set Filter Analysis
open Fields (pointMoment distinct)
open OS (Cross)
open scoped Topology BigOperators InnerProductSpace NNReal ContDiff
variable {F:Fields}{S:F.Kernel}{V:Chamber S timeAxis} (P: Spread V)
variable (H:Steady V) (Y:Fields.Euclidean S) (R:Angular S)
def orbit (K : EuPin) (x : Pack F) : Pack F := ⟨rotate x.val K,(trans R x.property K).1⟩

def world (K : EuPin) (x : Car F) : Car F := ⟨orbit R K x.1,Ortho.move K.coord ∘ x.2⟩
def stage (q : List (Pack F)) := inner ℂ V.omega0 ((starU P q).val V.omega0)

lemma whirl (q : List (Car F)) K (n) : all (q.map (world R K)) n=rotate (all q n) K := by
  have he (x : Cluster F) t : carry (rotate x K) (Ortho.move K.coord t) = rotate (carry x t) K := (rotated [] x K t).symm
  induction q with
  | nil => rfl
  | cons x q ih =>
    rw [show all (_ :: q) n=carry x.1.val (x.2 n) ++ all q n from rfl]
    change carry (rotate _ K) _ ++ all _ _=_
    rw [show ((world R K x).2 n)=_ from rfl] -- ...
    rw [ih]
    change carry (rotate _ K) (Ortho.move K.coord (x.2 n)) ++ _ = _
    rw [he]; unfold rotate; rw [List.map_append]

include H Y R
lemma alter (q v : List (Car F)) (z:ℂ) (hQ : line q) K (hK : line (v.map (world R K)))(hf:∀ i,distinct (all q i) → pointMoment S (all q i)=z*pointMoment S (all v i))(hd:∀ i,distinct (all q i) → distinct (all v i)) :
    stage P (q.map Prod.fst) = z * stage P ((v.map Prod.fst).map (orbit R K)) := by
  let f := q.map Prod.fst
  let g := world R K
  obtain ⟨hp,ht⟩ := arcs P H Y (v.map g) hK
  obtain ⟨hy,hs⟩ := arcs P H Y q hQ
  rw [show (List.map Prod.fst (v.map g))=(v.map Prod.fst).map (orbit R K) by simp only [List.map_map];rfl] at ht
  apply tendsto_nhds_unique (f:=fun i=>pointMoment S (all q i)) hs (((ht.const_mul z)).congr' ?_)
  filter_upwards[hy] with i hi; change z*pointMoment S (all (v.map (world R K)) i)=_; rw[whirl]
  rw[(trans R (hd i hi) K).2,hf i hi]

lemma same_up (k : EuPin) (x : E4) (hX : 0 < x timeAxis) (hx : 0 < Ortho.move k.coord x timeAxis) (q : List (Pack F)) :
    stage P q=stage P (q.map (orbit R k)) := by
  let G (i : Fin q.length) : Car F := ⟨q.get i, fun n => (n:ℝ) • ((i.val:ℝ) • x)⟩
  let Q := List.ofFn G
  have he (v : E4) (h : 0<v timeAxis) (i j : Fin q.length) (hi : i<j) :
      flight (fun n => (n:ℝ) • ((i.val:ℝ) • v)) (fun n => (n:ℝ) • ((j.val:ℝ) • v)) := by
    have hp : 0 < ((j.val:ℝ)-i.val)*v timeAxis := mul_pos (sub_pos.mpr (by exact_mod_cast hi)) h
    refine Tendsto.congr (fun n => ?_) (Tendsto.atTop_mul_const hp tendsto_natCast_atTop_atTop)
    simp; ring
  have hh : line Q := List.pairwise_ofFn.mpr fun _ _ h => he _ hX _ _ h
  have hy (i) : (world R k (G i)).2 = fun n : ℕ => (n:ℝ) • ((i.val:ℝ) • Ortho.move k.coord x) := by
    funext n; change (Ortho.motion k.coord) _ = _; rw [map_smul, map_smul];rfl
  have ht : line (Q.map _) := show line (Q.map (world R k)) from
    List.pairwise_map.mpr (List.pairwise_ofFn.mpr fun i j h => by
      rw [hy i,hy j]; exact he _ hx _ _ h)
  have hv := alter P H Y R Q Q 1 hh k ht (fun i _=> (one_mul _).symm) (fun _ ht=>ht)
  rw [show Q.map Prod.fst=q from by unfold Q; rw [List.map_ofFn]; exact List.ofFn_get .. ,one_mul] at hv; exact hv

-- need ONLY adjacent two middle of train of four
private def k : Signed := ⟨Equiv.swap timeAxis 0,fun _ => false⟩
omit H Y R in
private lemma switch_ax (p : E4) : Ortho.move k.ortho p timeAxis=p 0 := by simp [Signed.ortho_move,k,Signed.act]

omit H Y R in
private lemma boundOrder (w v : Car F) (t u : ℝ) (h : t<u) (hT : ∀ i, w.2 i timeAxis=i*t) (hU : ∀ i, v.2 i timeAxis=i*u) :
    flight w.2 v.2 := by
  simp_rw [flight,PiLp.sub_apply,hT,hU,← mul_sub]; exact Tendsto.atTop_mul_const (sub_pos.mpr h) tendsto_natCast_atTop_atTop

lemma exchanges (x y w z : Pack F) (Q D₀: List (Vose F)) (hB:Light Q) (hC:Light D₀)(hb:plain Q = y.val)(hc:plain D₀ = w.val): stage P [x,y,w,z]=bin (starb Q) (starb D₀) * stage P [x,w,y,z] := by
  have he (u v) : (u • basis timeAxis + v • basis 0) timeAxis=u ∧ Ortho.move k.ortho (u • basis timeAxis+v • basis 0) timeAxis=v := by simp [switch_ax] -- implicit u type
  let W (u v : ℝ) (q : Pack F) : Car F := ⟨q,fun i => (i:ℝ) • (u • basis timeAxis+v • basis 0)⟩
  have hx a b c d p q (h : a<b) : flight (W a c p).2 (W b d q).2 := boundOrder (W a c p) (W b d q) _ _ h (fun i => by simp [W]) (fun i => by simp [W])
  obtain ⟨q,hq⟩:= MassiveTwoEstimates.SpinGeometry.geometry.euclidean k.ortho
  let V := world R q
  have hy a b c d p q (h : c<d) : flight (V (W a c p)).2 (V (W b d q)).2 :=
    boundOrder _ _ _ _ h (fun i => by rw [show V (W a c p)=_ from rfl]; simp [W,V,world,hq,switch_ax])
      (fun i => by simp [W,V,world,hq,switch_ax])
  let A := W 0 0 x
  let B := W 1 2 y
  let C := W 2 1 w
  let D := W 3 3 z
  have hp : List.Perm [A,B,C,D] [A,C,B,D] := .cons _ (.swap ..)
  let ht := alter P H Y R [A,B,C,D] [A,C,B,D] (bin (starb Q) (starb D₀)) ?_ q ?_ ?_ (fun i hx=> locations.mpr (List.Perm.nodup (List.Perm.map Prod.fst ((hp.map (fun x : Car F=> carry x.1.val (x.2 i))).flatten)) (locations.mp hx)))
  · refine ht.trans ?_
    let v := (1:ℝ) • basis timeAxis+(1:ℝ) • basis 0
    refine congr_arg (_ * ·) (same_up P H Y R q v (show _ from (he 1 1).1 ▸ zero_lt_one) (show _ from ?_) _).symm; rw[hq]; exact (he 1 1).2 ▸ zero_lt_one
  · simp [line]; refine ⟨⟨hx 0 1 0 2 _ _ (by norm_num),hx 0 2 0 1 _ _ (by norm_num),hx 0 3 0 3 _ _ (by norm_num)⟩,
          ⟨hx 1 2 2 1 _ _ (by norm_num),hx 1 3 2 3 _ _ (by norm_num)⟩, hx 2 3 1 3 _ _ (by norm_num)⟩
  · simp [line]; refine ⟨⟨hy _ _ 0 1 _ _ (by norm_num),hy _ _ 0 2 _ _ (by norm_num),hy _ _ 0 3 _ _ (by norm_num)⟩,
       ⟨hy _ _ 1 2 _ _ (by norm_num),hy _ _ 1 3 _ _ (by norm_num)⟩, hy _ _ 2 3 _ _ (by norm_num)⟩

  intro i hi; let l:=carry x.val (A.2 i); let r:=carry z.val (D.2 i)
  have h₁: all [A,B,C,D] i=l ++ (plain (tranV Q (B.2 i)) ++ (plain (tranV D₀ (C.2 i)) ++ r)):=by simp only[remit,hb,hc]; exact congr_arg (fun v:Cluster F=> l ++ (carry _ _ ++ (carry _ _ ++ v))) (List.append_nil _)
  have h₂ : all [A,C,B,D] i = l ++ (plain (tranV D₀ (C.2 i)) ++ (plain (tranV Q (B.2 i)) ++r)):=by simp only[remit,hb,hc]; exact congr_arg (fun v:Cluster F=> l ++ (carry _ _ ++ (carry _ _ ++ v))) (List.append_nil _)
  rw [h₁] at hi ⊢; rw [h₂]; refine (relays Y l r _ _ (transV _ _ hB) (transV _ _ hC) hi).trans (by rw[stV,stV])
end YM.Massive.Bridge.Kly
#print axioms YM.Massive.Bridge.Kly.exchanges
