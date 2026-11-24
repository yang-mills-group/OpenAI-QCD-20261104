import YM.VStages.Bond
import YM.Massive.Stratum.Grind
/-!
# Itineraries, with parametric repetitions and arbitrary priced waystations

 Produces infinitely many distinct J's, gradual L's. Per-prototype arbitrary w
 fixed BEFORE setting plateau length; may choose extra padding after the usual
 thresholds on base coupling to inspect a long observation range. At each junction,
 really changes from H k to H(k+1) and graph repr contracts across the **intervening different J**
 in just one step (with possibly different post-L quantities than on either side).
 Uniform estimates on opacity trinkets/colors use only `relation`; time proofs of the actual
 operator step are still required.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Acre.Stratum.MarchQ
open Function Lattice RG Laurent Bloch Matrix Metric Precision Wilson Bid Craft Exterior Filter
open YM.Next.Free YM.Work YM.Further.PhysicalPeriodLimitF933
open WilsonStartup Design Change Extra.Iteration Stationary Tree Raft Garden Transfer Orbit Sparks Fog Birth Raft.ParcelR
open Flume Fog.Mist YM.Massive.Stratum Push ConnectedActivityE6 Pressure Pressure.Stores
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {j t k i l n N: ℕ}{K:KernelChoices}{p:ChangeQ→ChartRatio su}{h s:ℕ→ℕ}
    (P:Docket K h s)(J:(i:ℕ)→Plan (rank i))
open ChangeQ

def capPower (i:ℕ):Side:= (3:Side)^(i+1)
lemma widePower (i:ℕ) : 3 ≤ (capPower i).val:= by simpa [capPower,pow_succ] using pow_le_pow_right₀ (by decide :1≤(3:ℕ)) (show 1 ≤ i+1 from by omega)
lemma movePower : Tendsto (fun i=> (capPower i).val) atTop atTop:= (tendsto_pow_atTop_atTop_of_one_lt (by decide : 1<(3:ℕ))).comp (tendsto_add_atTop_nat 1)

def stepPower (i:ℕ)(q:ChangeQ):Flight q.old q.new:= ⟨capPower i,(show Odd (3:ℕ) from by decide).pow,widePower i,q.shape.1, by obtain ⟨-, -,h⟩:=q.shape; omega,by obtain ⟨-, -,h⟩:=q.shape; omega,Train.top q.old⟩
structure Enumerated where
  start:ℕ
  seam:ℕ→ChangeQ -- junction after holding for an arbitrary period
  meets k:(seam k).hi=(seam (k+1)).lo
  endless : Tendsto (fun k=>(seam k).lo) atTop atTop
abbrev Enumerated.nth (E:Enumerated)(k:ℕ):= (E.seam k).lo
abbrev Enumerated.rep (E:Enumerated)(k:ℕ):= stepPower (k+E.start) (steady (E.nth k))
abbrev Enumerated.bridge (E:Enumerated)(k:ℕ):= stepPower (k+E.start+1) (E.seam k)

-- simpler increments for Lit, allow staying as long as needed per plateau; growth of J happens on meeting any arbitrary L0 requirement at the next and at the transition.
theorem enumerating (f:ChangeQ→ℕ)(w:ℕ) :∃ E:Enumerated, E.nth 0=w ∧ (∀ k,f (steady (E.nth k)) ≤ (E.rep k).L.val) ∧ ∀ k,f (E.seam k) ≤ (E.bridge k).L.val:=by
  classical
  obtain ⟨u,h⟩:= eventually_atTop.mp (movePower.eventually_ge_atTop (f (steady w)))
  let g(k:ℕ): ℕ:= (capPower (k+u)).val
  have hg:Tendsto g atTop atTop:= movePower.comp (tendsto_add_atTop_nat _)
  let b(k i:ℕ):= (f (enter i) ≤ g (k+1) ∧ f (steady (i+1)) ≤ g (k+1))
  let Y := Nat.rec (motive:=fun _=>ℕ) w fun k a=> if b k a then a+1 else a
  have hY(k):Y (k+1)= if b k (Y k) then Y k+1 else Y k:=rfl
  have Hm : Monotone Y:= monotone_nat_of_le_succ fun i=> by rw [hY];split <;> omega
  have he(k): let z:=g k
              f (steady (Y k)) ≤ z:=by
       induction k with
       | zero=>exact h _ (Nat.le_add_left ..)
       | succ k ih=> rw [hY]; split
                     next hp=> exact hp.2
                     next hp=> exact ih.trans (by unfold g capPower; simp_rw [PNat.pow_coe]; apply pow_le_pow_right₀ (a:= (3:ℕ)) (by decide) (show k+u+1≤k+1+u+1 from by omega))
  let X(k):ChangeQ:= if b k (Y k) then enter (Y k) else steady (Y k)
  have hx(i):(X i).lo=Y i:=by unfold X; split <;> rfl
  have hz(i):(X i).hi=Y (i+1):=by unfold X; rw[hY]; split <;> rfl
  have H(i): ∃ k,i ≤ Y k:=by
       induction i with
       | zero=> exact ⟨0,Nat.zero_le _⟩
       | succ i ih=> obtain ⟨k,hk⟩:=ih; obtain ⟨j,hA,hB⟩:= ((hg.eventually_ge_atTop (max (f (enter i)) (f (steady (i+1))))).and (eventually_gt_atTop k)).exists
                     obtain ⟨j,rfl⟩:= Nat.exists_eq_succ_of_ne_zero (show j≠0 from by omega)
                     refine ⟨j+1,?_⟩
                     rcases lt_or_eq_of_le (hk.trans (Hm (show k ≤ j from by omega))) with hP|hP
                     · change i+1 ≤ Y (j+1); exact le_trans (show i+1 ≤ Y j from hP) (Hm (show j≤j+1 from by omega))
                     have hj : i = Y j:=hP
                     rw [hY, if_pos (show b j (Y j) from by rw [← hj]; exact max_le_iff.mp hA)]; omega
  let Z:Enumerated := {
    start := u
    seam:= X
    meets k := (hz k).trans (hx (k+1)).symm
    endless := by
       simp_rw [hx]; apply Filter.tendsto_atTop.mpr; intro i; obtain ⟨k,h⟩:=H i; filter_upwards [eventually_ge_atTop k] with j hj using h.trans (Hm hj) }
  refine ⟨Z,hx 0,fun k=> ?_,fun k=> ?_⟩
  · change f (steady ((X k).lo)) ≤ g k; rw[hx]; exact he k
  change f _ ≤ (capPower (k+u+1)).val; rw [show k+u+1=k+1+u by omega]
  change f (X k) ≤ g (k+1); unfold X; split; next h=> exact h.1
  next h=> have hu:=he (k+1); rw [hY,if_neg h] at hu; exact hu

-- Post allowances from prices: store Flight, X,Y, depend on p A. Small step radius.
structure Tag (P:Docket K h s)(J:(i:ℕ)→Plan (rank i))(p:ChangeQ→ChartRatio su) where
   node:ChangeQ
   flight: Flight node.old node.new
   fromX: Town
   toX: Town
   (c Θ:ℝ)
   fare :ParcelR
   supporting : FlightTicket P J node flight fromX toX (p node) c Θ fare
namespace Tag
variable {P J} (X:Tag P J p)
abbrev L:=X.flight.L
def NextOK (Y:Tag P J p):Prop:= X.node.hi=Y.node.lo ∧ X.fromX=Y.toX ∧ X.L.val ≤ Y.L.val ∧ Y.L.val ≤3*X.L.val
end Tag
-- Repeating sequence chunks. n adjacency payable. insert BEFORE exitQ lane exactly repeated `(repeat)`.
structure Depot (P:Docket K h s)(J:(i:ℕ)→Plan (rank i))(p:ChangeQ→ChartRatio su) (gate:ChangeQ→ℕ) where
   pillar :Enumerated
   fixed : ℕ → Tag P J p
   rounds : ℕ→ℕ
   blockEnd (i:ℕ): Fin (rounds i+1) → Tag P J p -- includes bridge shift
   tall (i:ℕ): (fixed i).node=steady (pillar.nth i) ∧ (fixed i).L=(pillar.rep i).L
   resource (i:ℕ): gate (fixed i).node ≤ (fixed i).L.val
   visits(i:ℕ): (fixed i).NextOK (fixed i)
   stares(i:ℕ): (fixed i).NextOK (blockEnd i 0)
   progresses (i:ℕ)(q:Fin (rounds i)): (blockEnd i q.castSucc).NextOK (blockEnd i q.succ)
   arrives (i:ℕ): (blockEnd i (Fin.last _)).NextOK (fixed (i+1))
   dates(i:ℕ)(q:Fin (rounds i)): (blockEnd i q.castSucc).node=(fixed i).node ∧ (blockEnd i q.castSucc).L=(fixed i).L
   changeNode (i:ℕ) : (blockEnd i (Fin.last _)).node=pillar.seam i ∧ (blockEnd i (Fin.last _)).L=(pillar.bridge i).L
   paid i q: gate (blockEnd i q).node ≤ (blockEnd i q).L.val
end YM.QCD.Acre.Stratum.MarchQ
