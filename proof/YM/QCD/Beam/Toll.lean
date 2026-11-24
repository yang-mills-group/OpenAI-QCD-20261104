import YM.QCD.Beam.Insertion
/-! # Sector molecule emission law with inserted Even tests -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Beam
open ConnectedActivityE6
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 ConnectedActivityE6.Shell
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary
open Coat
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f n : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}
variable {A W γ μ C : ℝ} {L : Side} {R : Rep G f} {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W}
variable (X : Coat T F) (k : Finset ℕ)
-- support license
lemma lending (K : Cash W X.x μ L Q o C T R) (hk:X.width=o.K) (Y : Finset (Stores S))(hX:X.approve k R) (h:Layout X.seeds Q.halo X.B Y) (z:Air f G) (hn:X.summedUp R Q.table W o.a z k Y ≠ 0): X.enforce o.a (X.liftA R.beta z) X.tier≠0:=by
    apply right_ne_zero_of_mul (a:=X.tangible R W (X.view (X.liftA R.beta z)) k*X.ribbons z Q.table R.beta o.a); change X.ticketK R W o.a Q.table z k≠_
    rw [X.consolidated k K hX.1 hk z h hX.2.1]
    have hp:= Matter.overhead_pos X K; unfold Matter.overhead at hp
    have hs:0 < X.thetaRef z:=by unfold thetaRef bell; positivity
    have he: X.levy R* X.deducted Q.table R.beta≠0 := ne_of_gt hp
    positivity

variable {M:Type*}[NormedAddCommGroup M][NormedSpace ℝ M]
lemma concrete {x y:M} (h : ∀ c:M→L[ℝ]ℝ,c x=c y): x=y:=by
    obtain ⟨c,hp,hy⟩ := exists_dual_vector'' ℝ (x-y); exact sub_eq_zero.mp (norm_eq_zero.mp (hy.symm.trans (by simp only [map_sub,h, sub_self])))
variable [CompleteSpace M][MeasurableSpace M][BorelSpace M][SecondCountableTopology M]
variable {ι: Type*}[MeasurableSpace ι]
lemma envPlot {g :ι→M}(h:Envelope g)(L :Measure ι) [IsFiniteMeasure L]:Integrable g L :=by
    obtain ⟨C,H⟩:=h.cost; exact Integrable.of_bound h.meas.aestronglyMeasurable C (Eventually.of_forall H)
lemma envDash (g :ι→M)(h:Envelope g)(f:ι→ℝ){L:Measure ι} (hp: Integrable f L): Integrable (fun i=> f i • g i) L :=by
    obtain ⟨z,hv⟩:= h.cost; apply (hp.norm.mul_const z).mono' (hp.aestronglyMeasurable.smul h.meas.aestronglyMeasurable)
    exact Eventually.of_forall fun i=> by change ‖f i • g i‖≤_; rw [norm_smul]; exact mul_le_mul_of_nonneg_left (hv i) (norm_nonneg _)
lemma shoreTaxi (m:F.Slice G→ℝ)(h : Integrable m (F.order G)) :
    (∫ Y,m Y ∂F.order G)= ∫ Y,∫ z,m ((X.wrapY Y).shifted z) ∂X.stages ∂F.order G:=by
  have he : Integrable (m ∘ X.shore.symm) _ := (X.propagation.symm.integrable_comp_emb
    X.shore.symm.measurableEmbedding).mpr h
  let g v := ∫ z,m (X.shore.symm (z,v)) ∂X.stages
  have hr : Integrable (fun w : (X.Signal → G.El) × (X.Fog→G.El) => g w.2) (X.stages.prod X.forecast) := he.integral_prod_right.comp_snd _
  rw [← X.propagation.symm.integral_comp' m]; symm
  rw [← X.propagation.symm.integral_comp' (fun Y=> ∫ z,m ((X.wrapY Y).shifted z) ∂X.stages)]
  simp_rw [Coat.shifted]
  change (∫ v, ∫ z,m (X.shore.symm (z,(X.shore (X.shore.symm v)).2)) ∂X.stages ∂_)=_
  simp_rw [X.shore.apply_symm_apply]; rw [Function.comp_def] at he; rw [integral_prod_symm _ hr, integral_prod_symm _ he]; simp [g]
lemma mile (K : Cash W X.x μ L Q o C T R) (hk:X.width=o.K)(hX:X.approve k R) (u: F.Slice G→M) (v:F.Slice G × Air f G→M)(hu:Envelope u)(hv:Envelope v)(ho:∀ Y z, let J:= X.wrapY Y; let p:=J.liftA R.beta z; J.enforce o.a p J.tier≠0 → v (Y,z) = u (J.view p)) (Y : Finset (Stores S))(h:Layout X.seeds Q.halo X.B Y) :
   (∫ Y,X.tangible R W Y k • u Y ∂F.order G)= X.tribute R Q.table • ∫ i:F.Slice G × Air f G,(X.wrapY i.1).summedUp R Q.table W o.a i.2 k Y • v i ∂((F.order G).prod X.dice):=by
    have he:= K.laws; have hp:=he.data
    let f0 w:= X.tangible R W w k • u w; let g (i:F.Slice G × Air f G):=(X.wrapY i.1).summedUp R Q.table W o.a i.2 k Y • v i
    have hF : Integrable f0 (F.order G):=envDash u hu _ ((Coat.sum_tangible X he.intake hp.W_pos hp.room.fiery).1 k)
    have hG : Integrable g _:=envDash v hv _ (X.uplink k Y K hk hX.1 h)
    apply concrete; intro l; change l (∫ w,f0 w ∂F.order G)= l (_ • ∫ i,g i ∂_)
    rw [map_smul, ← l.integral_comp_comm hF, ← l.integral_comp_comm hG]
    have hl := shoreTaxi X (fun w=>l (f0 w)) (l.integrable_comp hF)
    rw [hl, integral_prod _ (l.integrable_comp hG), ← integral_smul]; apply integral_congr_ae; filter_upwards with s
    have hu' :Measurable (l ∘ u):=l.measurable.comp hu.meas
    have hY (p): v (s,p)=u ((X.wrapY s).view ((X.wrapY s).liftA R.beta p)) ∨ (X.wrapY s).summedUp R Q.table W o.a p k Y=0:=by
       by_cases he' : (X.wrapY s).summedUp R Q.table W o.a p k Y=0; · exact Or.inr he'
       exact Or.inl (ho s p (lending (X.wrapY s) k K hk Y hX h p he'))
    unfold f0; simp_rw [map_smul]; rw [show (∫ z, X.tangible R W ((X.wrapY s).shifted z) k • l (u ((X.wrapY s).shifted z)) ∂X.stages)= _ from (X.wrapY s).ticketM K hX.1 hk k Y h hX.2.1 (l ∘ u) hu']
    change X.tribute R Q.table • _= X.tribute R Q.table • ∫ z,l (g (s,z)) ∂X.dice
    congr 1; apply integral_congr_ae; filter_upwards with p; unfold g; rcases hY p with h|h <;> dsimp only [Prod.fst, Prod.snd,Function.comp_apply]
    · rw [h,map_smul]; rfl
    rw [h]; simp
lemma evening (K : Cash W X.x μ L Q o C T R) (hk:X.width=o.K)(hX:X.approve k R) (u: F.Slice G→M) (v:F.Slice G × Air f G→M)(hu:Envelope u)(hv:Envelope v)(ho:∀ Y z, let J:= X.wrapY Y; let p:=J.liftA R.beta z; J.enforce o.a p J.tier≠0 → v (Y,z) = u (J.view p)) (Y : Finset (Stores S))(h:Layout X.seeds Q.halo X.B Y) : HasSum (fun t:ListsAt c f=> X.tribute R Q.table • ∫ i, X.body R Q.table W o.a k Q.halo (issue Y k t) i • v i ∂((F.order G).prod X.dice))
   (∫ Y,X.tangible R W Y k • u Y ∂F.order G) := by
      let g:=((F.order G).prod X.dice)
      let p t i := X.body R Q.table W o.a k Q.halo (issue Y k t) i • v i
      obtain ⟨C₀,ht⟩:=hv.cost
      have hs (t): Integrable (p t) g :=envDash v hv _ (K.integrated X rfl hk hX.1 k _)
      let H t:= (issue Y k t)
      have hp : Injective H:=by rintro ⟨i,j⟩ ⟨v,w⟩ he; simp [H,ConnectedActivityE6.issue] at he; exact Prod.ext he.2 he.1 -- simp?
      have he := (summable_finsetProd_of_summable_nonneg K.fair_price K.fair_summable).comp_injective hp
      have hy (t) (i:F.Slice G × Air f G) : ‖p t i‖≤ (∏ j∈ H t,K.fair j)* C₀:=by
         unfold p; rw [norm_smul]; exact mul_le_mul (K.every X rfl hk hX.1 k _ i.1 i.2) (ht i) (norm_nonneg _) (prod_nonneg fun _ _=> K.fair_price _)
      have hh : Summable fun t=>∫ i, ‖p t i‖ ∂g :=
         Summable.of_nonneg_of_le (fun _=> integral_nonneg fun _=> norm_nonneg _) (fun t=> by
            exact (integral_mono (hs t).norm (integrable_const _) (hy t)).trans_eq (integral_const _ |>.trans (by unfold g; simp))) (he.mul_right C₀)
      rw [mile X k K hk hX u v hu hv ho Y h]; have hx := hasSum_integral_of_summable_integral_norm hs hh
      have hh (i : F.Slice G × Air f G) : (∑' j,p j i)=(X.wrapY i.1).summedUp R Q.table W o.a i.2 k Y • v i:=(HasSum.smul_const (luxury (X.wrapY i.1) k K hk hX.1 h i.2) _).tsum_eq -- check
      simp_rw [hh] at hx; exact hx.const_smul _
end YM.QCD.Beam
