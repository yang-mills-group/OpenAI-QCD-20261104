import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Pane.Null
import YM.QCD.Port.Yard
/-!
# Reference vacuum for the relative gauge-fermion integral

The δ-characteristic is NONZERO in every fine-flag sector. Undo
only once per flag. (Not the output normalization.)
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Beam
open Function Lattice Wilson Tree RG Pressure Finset Filter
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid ConnectedActivityE6 SliceRows Mask Coat
open PhysicalNext.Repeat.Pane Kit
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {c f L:Side}{S:StepData c f}{T:Tube su S}{P:Teller su}{δ β τ μ:ℝ}
def mac (x: Site f):ℕ:= (keys f).symm (x,0)
lemma comes (x: Site f): abscissas f (mac x)=x:=by unfold abscissas mac; rw [Equiv.apply_symm_apply]
lemma minted (f:Side): Injective (mac (f:=f)):=LeftInverse.injective comes
lemma coversS (i:Site f)(b:ℕ): coverNumber b {i}=1:=by
   have h:= Animals.price_pos b ({i}:Support f) |>.mpr (singleton_nonempty _)
   have ht: coverNumber b ({i}:Support f)≤1:=le_trans (Lattice.Corona.list_cost (D:={i}) b ?_) (by simp)
   · exact le_antisymm ht h
   refine ⟨halo_subset ..,?_⟩
   apply Lattice.Corona.ship_halo; intro x hx y hy; simp only [mem_singleton] at hx hy; subst x y; exact .refl

def pearl (f:Side)(δ t:ℝ) : Activities su f := { pale f su with K:=fun i U=> if mac (abscissas f i)=i ∧ abscissas f i∈flags t U then δ else 0 }
lemma clearKx (t:ℝ)(U:Config su f)(x:Site f): x∉ flags t U→ (({x}:Support f)∩flags t U)=∅:=by intro h; ext; simp; grind
lemma sparkB (t:ℝ)(x:Site f)(V W:Config su f)(h:({x}:Support f)∩flags t V={x}∩flags t W): (x∈flags t V↔x∈flags t W):= by
   have he: x∈({x}:Support f)∩flags t V ↔ x∈({x}:Support f)∩flags t W := by rw [h]
   simpa using he
lemma gerund (b:BudgetPoint)(f:Side)(δ:ℝ): let R:=pearl f δ b.threshold; R.Valid b 0 (Real.exp (b.supportExponent)*|δ|) := by
   intro R; let V:=pale f su; let A:=abscissas f; have hx:= whey f su b; let t:=b.threshold
   refine ⟨⟨hx.regular.smooth,hx.regular.at_flat,hx.regular.vanish⟩,?_,?_,hx.boundE,?_⟩
   · refine ⟨fun i U V=> ?_,fun _ _ _ => Iff.rfl, fun i=>?_,fun _=>MeasurableSet.univ,fun i U V _ ht=>?_,fun _ _ _ _ _=>rfl,fun i U h => ?_⟩
     · dsimp only [R,pearl]; simp only [gauge_flags]
     · change Measurable (fun U: Config su f=> if mac (A i)=i∧ _ then _ else _)
       by_cases he:mac (A i)=i
       · simp only [he,true_and]; exact Measurable.ite ((flags_open _ _).measurableSet) measurable_const measurable_const
       simp only [he,false_and, if_false]; exact measurable_const
     · have he:= sparkB t (A i) U V ht; exact if_congr (and_congr Iff.rfl he) rfl rfl
     change (if _ then _ else _)≠_ at h
     by_cases hi : mac (A i)=i∧ A i ∈flags t U
     · exact ⟨(inter_eq_left.mpr (singleton_subset_iff.mpr hi.2)),trivial⟩
     exact False.elim (h (if_neg hi))
   · intro s v; let u := Equiv.prodCongr (StepData.sendSites s v) (Equiv.refl ℕ); let e:=keys f; let p: Equiv.Perm ℕ:= (e.trans u).trans e.symm
     have he (w:Site f): p (mac w)=mac (affine s v w):= e.injective (by simp [p,e,u,mac]; rfl)
     have hy i : abscissas f (p i)=affine s v (abscissas f i) := congr_arg Prod.fst (show e (p i)=u (e i) from e.apply_symm_apply _)
     have hv i : ({abscissas f (p i)}:Support f)= image (affine s v) {abscissas f i}:= by simp [hy]
     refine ⟨⟨p,p,hy,hv,hv,hv, fun _ _=> Iff.rfl, fun _ _=>rfl, fun i U=>?_⟩⟩
     dsimp only [R,pearl]; rw [hy,← he, ← Work.H03.flags_send (G:=su) s v b.threshold U]; simp only [Equiv.apply_eq_iff_eq]
     have hh : Injective (affine s v):= (StepData.sendSites s v).injective
     apply if_congr _ rfl rfl
     apply and_congr Iff.rfl
     exact ⟨fun ha=> by obtain ⟨z,hz,hQ⟩:= mem_image.mp ha; exact hh hQ ▸ hz,fun h=> mem_image_of_mem _ h⟩
   · let g (i:ℕ) := if mac (A i)=i then |δ| else 0; let k:= Real.exp (b.supportExponent)*|δ|
     have hk:0≤k:=by unfold k; positivity
     refine ⟨g,fun i=>?_,fun x=>?_⟩
     · refine ⟨by unfold g; split; exact abs_nonneg _; exact le_rfl,fun U=>?_⟩
       dsimp only [R,pearl]; rw [Real.norm_eq_abs]; split
       next h=> exact le_of_eq (if_pos h.1).symm
       next he=> rw [abs_zero]; unfold g; split; exact abs_nonneg _; exact le_rfl
     have hu: HasSum (Pi.single (mac x) k : ℕ→ℝ) k:=by
        have ht := hasSum_single (f:=(Pi.single (mac x) k : ℕ→ℝ)) (mac x) (fun i h=>Pi.single_eq_of_ne h _); rw [Pi.single_eq_same] at ht; exact ht
     have he: SumBudget (Pi.single (mac x) k) k:= by
       refine ⟨?_,hu.summable,hu.tsum_eq.le⟩
       intro i
       by_cases ht:i=mac x
       · subst i; rwa [Pi.single_eq_same]
       rw [Pi.single_eq_of_ne ht]
     convert! he using 1
     funext i; change (if x∈({abscissas f i}:Support f) then b.mass {abscissas f i} (g i) else 0)=_; simp only [mem_singleton]; split_ifs with hh
     · rw [BudgetPoint.mass, coversS,Nat.cast_one,mul_one]; unfold g; split
       next hi=> change mac (abscissas f i)=i at hi; rw [← hh] at hi; rw [← hi, Pi.single_eq_same]
       next hi=> have he: i≠mac x:=fun h=> hi ((congr_arg mac hh.symm).trans h.symm); rw [Pi.single_eq_of_ne he,mul_zero]
     rw [Pi.single_eq_of_ne (show i≠mac x from fun hp=> hh (hp ▸ (comes x).symm))]
variable {x:ℝ} {i:Site f}
def typo (Y:Support f):=Y.image mac
lemma keynote (Y:Support f) (U:Config su f) (R: BudgetPoint) (δ:ℝ): let V:=pearl f δ R.threshold; V.gasOccurrence R (typo Y) U= if Y=flags R.threshold U then δ^Y.card else 0:=by
   intro V
   have he : (typo Y).biUnion (fun i=>(V.forced i).inventory)= Y:=by
     ext i; simp only [mem_biUnion,typo, mem_image]; constructor
     · rintro ⟨j,⟨z,hz,rfl⟩,hh⟩; change i ∈ ({abscissas f (mac z)}:Support f) at hh; rw [comes, mem_singleton] at hh; exact hh ▸ hz
     exact fun h=>⟨_,⟨i,h,rfl⟩,mem_singleton.mpr (comes i).symm⟩
   have hv : V.admissible R U (typo Y) ↔ Y= flags R.threshold U:=by
      unfold Activities.admissible; rw [he]; refine ⟨fun h=>h.2,fun h=>⟨?_,h⟩⟩
      intro i hi j hj hs; obtain ⟨i,hi,rfl⟩:=mem_image.mp hi; obtain ⟨j,hj,rfl⟩:=mem_image.mp hj
      change Disjoint ({abscissas f (mac i)}:Support f) {abscissas f (mac j)}; rw [comes,comes]; exact disjoint_singleton.mpr (fun h=>hs (congr_arg _ h))
   unfold Activities.gasOccurrence; split
   next h=> rw [if_pos (hv.mp h),typo,prod_image]; swap; · exact fun _ _ _ _ he=> minted f he
            rw [prod_congr rfl (show ∀ i∈Y,_= (fun _=> δ) i from fun i hi=>?_ ),prod_const]
            change (if _ then δ else 0)=_; apply if_pos; exact ⟨congr_arg _ (comes i), (comes i).symm ▸ ((hv.mp h) ▸ hi)⟩
   next h=> rw [if_neg (mt hv.mpr h)]
lemma hardy (R:BudgetPoint)(δ:ℝ)(U:Config su f): let V:=pearl f δ R.threshold; V.gas R U= δ^(flags R.threshold U).card :=by
   intro V; unfold Activities.gas; rw [tsum_eq_single (typo (flags R.threshold U)),keynote]; simp
   intro b hb; by_contra ha
   unfold Activities.gasOccurrence at ha; split at ha
   next he=>
    have hv j (hj:j∈b) : V.K j U≠0:= fun H=>ha (prod_eq_zero hj H)
    have hΔ j (hj:j∈b): mac (abscissas f j)=j∧abscissas f j∈flags R.threshold U:= by_contra fun hh=> hv j hj (if_neg hh)
    apply hb; unfold typo; ext i; constructor
    · intro hi; exact mem_image.mpr ⟨_,(hΔ i hi).2,(hΔ i hi).1⟩
    intro hi; obtain ⟨k,hk,rfl⟩:=mem_image.mp hi; rw [← he.2] at hk; obtain ⟨j,hj,h⟩:= mem_biUnion.mp hk; rw [mem_singleton.mp (show k ∈ ({abscissas f j}:Support f) from h),(hΔ j hj).1]; exact hj
   exact ha rfl
lemma windy (t:ℝ)(P:BudgetPoint)(W:Config su f) : (pearl f δ t).additive P W =0:=(PhysicalNext.Repeat.Pane.pale_value P W).1
def trimP (T:Tube su S)(P:BudgetPoint)(δ β t:ℝ):Rep su f:=⟨T.up,T.high,pearl f δ P.threshold,P,β,t⟩
lemma portrait (T:Tube su S)(R: BudgetPoint)(β t δ:ℝ)(U:Config su f) : (trimP T R δ β t).eval U= Real.exp (t* Fintype.card (Site f)- T.up.inChannels T.high R β U)* δ^(flags R.threshold U).card:=by
   unfold Rep.eval Rep.exponent; dsimp only [trimP]; rw [windy, hardy]; simp
lemma climate (x:ℝ)(T:Tube su S)(R: BudgetPoint)(t:ℝ) (hR :R.threshold=fiery su x S.patch.L) (hp :P.top.supportExponent=R.supportExponent) (h :P.Funds S T) (hm : 1<betaF su x S.patch.L) (he : R.B=radiusB (betaF su x S.patch.L)) (hx :betaF su x S.patch.L/2 ≤ β∧β ≤2*betaF su x S.patch.L) (ht : T.up.Bounds T.high P.top.width P.top.paths (loopBill su S.patch.L x)) (hF : Real.exp R.supportExponent*|δ| ≤ incomingK su S.patch.L x):Intake P T x (trimP T R δ β t) :=by
   have hy:=gerund R f δ
   exact ⟨h,⟨rfl,rfl,hR⟩,⟨ht,{hy with boundE:= YM.AnalyticBridge.VerifiedReset.Time.E_rises hy.boundE (by unfold incomingE; positivity),boundK:= YM.AnalyticBridge.VerifiedReset.Time.K_rises hy.boundK hF}⟩,hp,hm,he,hx⟩
end YM.QCD.Beam
