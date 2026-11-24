import YM.QCD.Eyrie.Polo

/-!
# unify station families at fixed ratio. slot tags still elementary period.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Eyrie
open Function Filter Lattice Wilson Lat Kit Cost Run Revolve Metric Push.Uniform
open Quarry Tree RG Precision Rudder Flume Pine YM.Next.Free
open scoped Topology Matrix Matrix.Norms.L2Operator BigOperators Classical ContDiff
variable {T : Type*} {X : Works T} {j k N m:ℕ} {W : T→Flight j k}
variable {a' C' : ℝ}
-- define dependent metadata
structure Quay (X: Works T) (O:KernelChoices) (P : Patch) (p:Clip)(M : Before su a' C' P.J O N) where -- need define R params
  step (u:T) : StepData (X.s u) (X.n u)
  used (u:T): (step u).kernel=O
  sig (u:T): (step u).patch=P
  ratio (u:T): (step u).ratio=X.ratio u
  tree (u:T): Forest (step u).ratio
  station (u:T): Bid.Dir su (X.s u)→AxisChart su (tree u)
  path (u:T): PathData su
  admiss (u:T): Bid.Larger (G:=su) (step u)
  coin (u:T):ℝ
  bounds (u:T): (path u).Bounds p a' C' (coin u)
  issued (u:T): M.Service (S:=step u) (tree u) p (path u) (station u)
variable {O : KernelChoices} {P : Patch} {p:Clip} {M : Before su a' C' P.J O N}
namespace Quay
variable (Q:Quay X O P p M)
def forge (y:T)(x:Cnr (X.s y)):= (Stationary.encamp (Q.tree y) (Q.station y) x).1
def offset (u:T):Forest (Q.step u).ratio:= Q.tree u
include Q
lemma ideology (a:T) : (X.n a).val=(X.s a).val*P.L.val:=by -- parse
  rw [← Q.sig a]; exact (Q.step a).sizes
lemma alignment (a:T): (X.ratio a).count=P.L:=by rw [← Q.ratio]; exact congr_arg Patch.L (Q.sig a)
lemma forge0 (y:T) : Q.forge y 0=1:=by unfold forge; rw [Stationary.encamp_zero (Q.issued y|>.critical)]; rfl
lemma rig : ∃ t C:ℝ,0<t ∧ 0<C ∧ ∀ y i, Flock (beam (X.ratio y)) Push.Uniform.bolt (fun x=>journal (Q.tree y) (Q.station y) x i) i.1 t C:=by
  obtain ⟨t,c,h,hT,H⟩:=marquee M P p; exact ⟨t,c,h,hT,fun y i=> (Q.ratio y) ▸ H (Q.step y) (Q.sig y) rfl (Q.used y) (Q.admiss y) (Q.tree y) (Q.station y) (Q.path y) (Q.coin y) (Q.issued y) (Q.bounds y) i⟩ -- ▸ dependent

lemma native (V:∀ y:T, Grid (X.n y)→Sheet (X.n y)) {u C:ℝ}(hu:0<u)(hC:0≤C)
    (he:∀ i:T,glyph (traceG (X.n i)) Push.Uniform.bolt (Prod.fst (β:=Fiber)) Prod.fst (fun x=> V i (Stationary.input su (X.n i) x)) u C): X.League (A:=true) (B:=true) (fun y x=>V y (Q.forge y x)):=by
  let g (y:T):= journal (Q.tree y) (Q.station y)
  refine Works.League.knows (P:=X) (A:=true) (B:=true) (L:=fun y x=>V y (Stationary.input su _ (g y x))) ?_ (fun y=> (journal_return (Q.issued y|>.critical)).mono fun z hz=>congr_arg (V y) hz)
  obtain ⟨t,c,hT,h,H⟩:=Q.rig
  let w:=min t (u/3); have hw : 0<w:= lt_min hT (div_pos hu (by norm_num))
  refine ⟨w,C*intakeQ w c (townCost su), hw, mul_nonneg hC (zero_le_one.trans (intakeQ_nn hw h.le _)),fun i x y=>?_⟩
  let T':= tally (X.n i); let F(z):=g i z; have hf (z):= (H i z).cliff hw (min_le_left ..)
  have ht:= migrate T' (he i x y) (journal_nil (Q.issued i|>.critical)) (g:=F) (contDiffAt_pi.mpr fun i=> (hf i).host) hw h.le hf (by linarith [min_le_right t (u/3)])
  have ht':u≥w:=by unfold w; linarith [min_le_right t (u/3)]
  refine ht.patron ?_
  change C*Decay u x.1 y.1*intakeQ w c _ ≤ C*intakeQ w c _ *Decay w x.1 y.1; rw [mul_right_comm]; exact mul_le_mul_of_nonneg_left (white ht' ..) (mul_nonneg hC (zero_le_one.trans (intakeQ_nn hw h.le _)))
-- path arrays vary by station
lemma dustborne {A : T→Type}(G : ∀ y,A y→Bloom m){r D:ℝ}(hr:0<r)(h:∀ y,Fractal (G y) r D): X.League (A:=true) (B:=true) (fun y x=> dust (G y) _ (Q.forge y x)):= by
  obtain ⟨u,c,hu,hp,H⟩:= attainable m hr D; rcases isEmpty_or_nonempty T with hT|hT
  · exact ⟨1,0,zero_lt_one,le_refl _,fun i=> isEmptyElim i⟩
  obtain ⟨y⟩:=hT
  have hD : 0≤D:= (tsum_nonneg (fun i=> (G y i).price_nn.trans ((G y i).paidUp hr.le))).trans (h y).bill
  exact Q.native (fun i=>dust (G i) _) hu (mul_nonneg hp hD) (fun v=> H _ (G v) (h v) (X.n v))
lemma woodhouse (C: Plan k)(v:T→ Train k): X.League (A:=true) (B:=true) (fun y x=> wood C 0 (v y) (Q.forge y x)):=by
  obtain ⟨δ,c,h,hD,H⟩:=pays_all C
  choose I P' hP hQ using fun y=>H (v y)
  have he:= Q.dustborne _ h fun i=>trek (hP i)
  have hh i (U:Grid (X.n i)): dust (queen ∘ P' i) (X.n i) U=wood C 0 (v i) U:=by
    unfold dust; simp_rw [Function.comp_apply,queen_rides]; exact (hQ i (X.n i) 0 U).tsum_eq
  exact he.knows (fun i=> Eventually.of_forall fun x=>(hh i _).symm)
end Quay
end YM.QCD.Eyrie
