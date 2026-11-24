import YM.QCD.Beam.Toll
/-! # at fixed dummy K. No Haar division at flags. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Beam
open ConnectedActivityE6
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open PhysicalNext.Repeat.Pane Presented LabelSum Matter
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L:Side}{S:StepData c f}{T:Tube G S}{P:Teller G}{δ β τ μ W C:ℝ} {R:Rep G f}{F:Forest S.ratio}{Q:Target G P}{o :Target.Order G W}
variable {M:Type*}[NormedAddCommGroup M][NormedSpace ℝ M][CompleteSpace M][MeasurableSpace M][BorelSpace M][SecondCountableTopology M]
-- proper even extension
lemma pill (T:Tube G S)(R:Rep G f)(t:ℝ) (k : Finset ℕ)(V:Config G c)(U:Config G f)(i:S.Choices)(h:Fits T R t):
    sieve T R.beta t V*separate R (till t) k U*enters T R.beta t i V U = taggedKernel S R.beta i U V * (Real.exp (R.exponent U)*R.activities.gasOccurrence R.p k U):=by
   unfold sieve separate enters; let A:=R.activities.gasOccurrence R.p k U
   let B:= averaged fun s =>∑ j, crown T.down T.low (till t) S.patch.L.val (temp t) (pull s 0 V) j
   have hl: wholeGap T t U V=cutR R (till t) U - B:=by unfold wholeGap Next.Fluctuations.Sector.crownGap cutR B; rw [h.clip,h.path,h.temp]; exact av_sub ..
   rw [hl]
   let b:= R.beta
   let c:= cutR R (till t) U
   have he: Real.exp (-b*B)*Real.exp (b*c)*Real.exp (-b*(c-B))=1:=by rw [← Real.exp_add,← Real.exp_add]; ring_nf; rw [Real.exp_zero]
   unfold b B c at he; unfold B; linear_combination taggedKernel S R.beta i U V*Real.exp (R.exponent U)*R.activities.gasOccurrence R.p k U*he -- negative notation
lemma legacy (X:Coat T F)(K:Cash W X.x μ L Q o C T R)(k s): X.tangible R W s k=X.χ.distribute X.seeds X.x W (F.drape s) X.k X.V *(taggedKernel S R.beta X.k (F.drape s) X.V*(Real.exp (R.exponent (F.drape s))*R.activities.gasOccurrence R.p k (F.drape s))):=by unfold tangible; dsimp only; rw [← pill T R _ k _ _ X.k K.laws.intake.received]; unfold Coat.R; ring
lemma unready (X:Coat T F)(K:Cash W X.x μ L Q o C T R)(k:Finset ℕ) (h:¬X.approve k R)(s): X.tangible R W s k=0:=by
    by_contra hn; apply h
    have hr:= K.laws
    let Z:= X.χ.profiles G S X.x W hr.data.W_pos hr.data.room.fiery
    have hu : Z.bill X.seeds X.k (F.drape s) X.V≠0 := right_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul hn))
    have hj : R.activities.gasOccurrence R.p k (F.drape s) ≠ 0 := right_ne_zero_of_mul (right_ne_zero_of_mul (left_ne_zero_of_mul hn))
    have hh:= Contract.needs hr.intake k Z _ _ _ hu hj; rw [Contract.release hr.intake] at hj; refine ⟨(Z.actual _ _ _ _ hu).exactFlags,(by by_contra hg; exact hj (if_neg hg)),hh⟩
-- theorem holdR only root gauge
lemma rooted (F:Forest S.ratio)(R:Rep G f)(k:Finset ℕ)(V:Config G c)(D:Allocation G S τ W)(f':Config G f→M)(X : Config G f→M) (hr : S.patch.Branches S.kernel G)
 (h:∀ U,X U= (Real.exp (R.exponent U)*R.activities.gasOccurrence R.p k U) • f' U)(hi:Envelope X) (ht : ∀ g:Site f→G.El,(∀ i,g (S.ratio.embed i)=1) → ∀ U,X (Lattice.gauge g U)= X U):
    (∑ i:Stores S, output D F R.beta X i V)= S.push R.beta X V :=by
    let q:=R.beta
    let Y:S.Choices→F.Slice G→M:=fun _ a=>X (F.drape a)
    have hg k: Integrable (through S F q V Y k) (F.order G):= through_integrable F q V Y hr k (envPlot (Env.along hi F.continuous_drape.measurable) _)
    have he:S.push R.beta X V= ∫ Y : F.Slice G, S.density q (F.drape Y) V • X (F.drape Y) ∂F.order G:=by
       refine F.pack _ (StepData.push_slice (S.isKernel hr q) V X (envPlot hi _)) fun k h U=>?_
       have he :Lattice.gauge (k ∘ S.ratio.embed) V=V:=by funext; simp [Lattice.gauge,h]
       rw [← S.covary hr k q U V,he, ht k h]
    rw [he]; change (∑ i,D.column i F V (through S F R.beta V Y))= _
    rw [D.partitions hr F V _ hg]; unfold tagTotal; rw [← integral_finsetSum _ fun i _=> hg i]
    apply integral_congr_ae; filter_upwards with a; unfold SectorMeasure.through StepData.density taggedKernel Y; rw [Finset.sum_smul]

lemma lapis {ι κ : Type*} [Fintype κ] [FiniteDimensional ℝ M] (w : κ × ι → M) (a : κ → M) (h : ∀ i, HasSum (fun j => w (i,j)) (a i)) : HasSum w (∑ i,a i) := by
  have hw : Summable w:=((summable_prod_of_nonneg (show 0 ≤ (fun i=> ‖w i‖) from fun _=> norm_nonneg _)).2
     ⟨fun i=> (h i).summable.norm,(hasSum_fintype _).summable⟩).of_norm
  convert hw.hasSum using 1; rw [hw.tsum_prod,tsum_fintype]; simp_rw [(h _).tsum_eq]

variable (X:Coat T F)(k:Finset ℕ) (u:F.Slice G→M) (v:Coat T F→Air f G→M)
def cellMean (R:Rep G f) (Q:Target G P)(W a:ℝ) (X: Coat T F)(m:Molecule S) (k:Finset ℕ)(v: Coat T F→ Air f G→M): M:=∫ i: F.Slice G × Air f G,X.body R Q.table W a k Q.halo m i • v (X.wrapY i.1) i.2 ∂((F.order G).prod X.dice)
def welcome (R:Rep G f)(Q:Target G P)(W a:ℝ)(X:Coat T F)(k:Finset ℕ)(v:Coat T F→Air f G→M) (m : Molecule S):= (Fintype.card S.Choices:ℝ)⁻¹ • ∑ i:S.Choices,cellMean R Q W a (X.taggedL i) m k v

def decree (R:Rep G f)(Q:Target G P)(W a:ℝ)(X:Coat T F)(v: Coat T F →Air f G→M)(m:Molecule S): M:=if h : (preps X (roster m)).approve (own m) R ∧ Layout (roster m) Q.halo X.B m.toLeft then welcome R Q W a (preps X (roster m)) (own m) v m else 0

set_option maxHeartbeats 1200000 in
lemma sherpa [FiniteDimensional ℝ M] (K:Cash W X.x μ L Q o C T R)(hk:X.width=o.K) {f':Config G f→M}(hu:Envelope f') (hv:∀ (A:Stores S)(w:S.Choices), let Z:=(preps X A).taggedL w; Z.approve k R→Envelope (fun i:F.Slice G × Air f G=>v (Z.wrapY i.1) i.2)) (ho:∀ (A:Stores S)(w:S.Choices)Y z, let Z:=(preps X A).taggedL w; let J:=Z.wrapY Y; Z.approve k R → let p:=J.liftA R.beta z; J.enforce o.a p J.tier≠0 → v J z=f' (J.input p)) :
    let D:=X.χ.profiles G S X.x W K.laws.data.W_pos K.laws.data.room.fiery
    let X' U := (Real.exp (R.exponent U)* R.activities.gasOccurrence R.p k U) • f' U
    HasSum (fun m:Molecule S=> if own m=k then overhead X R Q.table • decree R Q W o.a X v m else 0) (∑ i:Stores S,output D F R.beta X' i X.V):=by
  intro D X'; let f'':= fun m:Molecule S=> if own m=k then overhead X R Q.table • decree R Q W o.a X v m else (0:M)
  let U (z: Stores S × ListsAt c f):= crew S Q.halo X.B (z.1,k,z.2)
  have hg z: obtainBack (U z)=(z.1,k,z.2):= deposit (S:=S) _
  have hi : Injective U:= by
     intro x y he; exact Prod.ext (congr_arg (fun z:Packed S=> z.1) ((hg x).symm.trans ((congr_arg obtainBack he).trans (hg y)))) (congr_arg (fun i:Packed S=>i.2.2) ((hg x).symm.trans ((congr_arg obtainBack he).trans (hg y))))
  apply (hi.hasSum_iff (f:=f'') (fun i h=>?_)).1
  · apply lapis
    intro a
    let g (z:S.Choices):= (preps X a).taggedL z
    let N l:= U (a,l)
    let Y:= preps X a
    have hw i: Y.approve k R↔ (g i).approve k R:=Iff.rfl
    let L:=Layout.rolls a Q.halo X.B
    let F'(l:ListsAt c f)(i:S.Choices):M:= if (g i).approve k R then (g i).tribute R Q.table • cellMean R Q W o.a (g i) (N l) k v else 0
    have hx (i:S.Choices): HasSum (fun l=>F' l i) (∫ y,D.portion a F X.V (through S F R.beta X.V (fun _ b=> X' (F.drape b))) i y ∂F.order G) := by -- signature
       let Z:=g i
       have hz : (∫ y,D.portion a F X.V (through S F R.beta X.V (fun _ b=> X' (F.drape b))) i y ∂F.order G)= ∫ y,Z.tangible R W y k • f' (F.drape y) ∂F.order G:= by
         unfold SectorMeasure.Allocation.portion; apply integral_congr_ae; filter_upwards with y
         rw [legacy (g i) K]; unfold SectorMeasure.through X'; rw [mul_smul,mul_smul]; rfl
       rw [hz]; by_cases ht :(g i).approve k R
       · simp only [F',if_pos ht]
         have hq := evening (g i) k K hk ht (fun y=> f' (F.drape y)) (fun j=>v (Z.wrapY j.1) j.2) (Env.along hu F.continuous_drape.measurable) (hv _ _ ht) (fun _ _=>ho a i _ _ ht) _ (Layout.enlists a Q.halo X.B)
         change HasSum (fun l: ListsAt c f=> (g i).tribute R Q.table • cellMean R Q W o.a (g i) (ConnectedActivityE6.issue L k l) k v) _ at hq
         have HH l: N l=ConnectedActivityE6.issue L k l:=rfl
         simp_rw [HH]; exact hq
       simp only [F',if_neg ht]; simp_rw [unready Z K k ht,zero_smul,integral_zero]; exact hasSum_zero
    have hh (l): (f'' (U (a,l)))=∑ i:S.Choices,F' l i:=by
       have hY : roster (N l)=a:=congr_arg (fun z:Packed S=> z.1) (hg (a,l))
       have hS : own (N l)=k:=congr_arg (fun p:Packed S=>p.2.1) (hg (a,l))
       have hL : Layout a Q.halo X.B (N l).toLeft:=by
          rw [show (N l).toLeft=L from Finset.toLeft_disjSum ..]; exact Layout.enlists a Q.halo X.B
       have he i : (g i).tribute R Q.table= overhead X R Q.table*(Fintype.card S.Choices:ℝ)⁻¹ :=by
           rw [← Matter.visitsM X a i]; unfold tribute g overhead; ring
       change f'' (N l)=_; unfold f''; rw [if_pos hS,decree,hS,hY]; by_cases hx:Y.approve k R
       · rw [dif_pos ⟨hx,hL⟩,welcome]; simp_rw [F', if_pos (hw _ |>.mp hx),he,mul_smul, Finset.smul_sum]; rfl
       rw [dif_neg (fun h=>hx h.1),smul_zero]; have hu i: ¬(g i).approve k R:= mt (hw i).mpr hx; simp only [F',if_neg (hu _),sum_const_zero]
    convert! hasSum_sum (s:=univ) (fun i _=>hx i) using 1; exact funext fun i=>hh i
  unfold f'' decree; by_cases he:own i=k
  · rw [if_pos he]; rw [dif_neg (fun hv=> h ⟨(roster i,(obtainBack i).2.2), show U _=i from by unfold U; rw [← he]; exact recovery hv.2⟩), smul_zero]
  rw [if_neg he]
end YM.QCD.Beam
