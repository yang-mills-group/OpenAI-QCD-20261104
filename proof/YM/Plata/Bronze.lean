import YM.Plata.Scale
/-! The ground characters on the chosen chamber ALL satisfy authentic inequality. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section
namespace YM.Plata
open Function Set Filter Metric MeasureTheory Lattice Wilson Massive Massive.Lyre Massive.Romance Goblet
open QCD QCD.Lat -- no Fields
open Patria Patria.Depth Patria.Hub Patria.Exposure
open UV Needle
open YM.Fir Massive.Fir NoteF Tarn Choir Analysis
open Bridge (reflect Cluster carry Spread Chamber realize)
open Bridge.Kly (arcs Pack Car line stage Steady dome M bloom)
open OS.Ground (Panes)
open Massive.Fields (pointMoment)
open scoped Topology BigOperators Classical ComplexOrder InnerProductSpace
private lemma exponent {X:Type*} [TopologicalSpace X][MeasurableSpace X][BorelSpace X][CompactSpace X] (μ:Measure X)[IsProbabilityMeasure μ] [μ.IsOpenPosMeasure] (b:X→ ℂ)(hb:Continuous b){R:ℝ}(hr:0 ≤ R)(h:∀ n:ℕ,(∫ x, (‖b x‖^2)^n ∂μ)≤ R^(n*2)): ∀ x,‖b x‖ ≤ R:=by
        intro x; by_contra! he; obtain ⟨p,hp,hp'⟩:=exists_between he
        let U:= b ⁻¹' {x:ℂ|p<‖x‖}; have hP : 0 < p:=hr.trans_lt hp; have hT:IsOpen U:= (isOpen_lt continuous_const continuous_norm).preimage hb
        let y:= μ.real U; have hy:0< y:= ENNReal.toReal_pos (hT.measure_pos (μ:=μ) ⟨x,hp'⟩).ne' (measure_ne_top _ _)
        let z:= R^2/p^2; have hh:0 ≤z:= div_nonneg (by positivity) (by positivity); have hf:Tendsto (fun n:ℕ=>z^n) atTop (𝓝 0):= tendsto_pow_atTop_nhds_zero_of_lt_one hh (by apply (div_lt_one (pow_pos hP _)).mpr; nlinarith)
        obtain ⟨n,hv⟩:=(hf.eventually_lt_const hy).exists; have hh': Continuous (fun x:X=>(‖b x‖^2)^n):=(hb.norm.pow _).pow _
        have hI: (∫ x, U.indicator (fun _:X=>(p^2)^n) x ∂μ) ≤ R^(n*2):=by
             refine (integral_mono ((integrable_const _).indicator hT.measurableSet) (hh'.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace ..)) (fun x=>?_)).trans (h n); by_cases hx:x∈U; · rw [indicator_of_mem hx]; exact pow_le_pow_left₀ (sq_nonneg _) (pow_le_pow_left₀ hP.le (show p≤ ‖b x‖ from hx.le) _) _ -- hx reducible lt
             rw [indicator_of_notMem hx]; exact pow_nonneg (sq_nonneg _) _
        rw [integral_indicator hT.measurableSet,setIntegral_const, smul_eq_mul, Nat.mul_comm,pow_mul] at hI; have hx: y ≤ z^n:=by unfold z; rw [div_pow]; exact (le_div_iff₀ (by positivity)).mpr hI
        linarith
noncomputable def beats : ℕ→List Bool | 0=> [] | n+1=>true::false:: beats n
lemma beating(L:ℕ):(beats L).length=L*2:=by induction L with|zero=>simp [beats]|succ n ih=> rw [beats,List.length_cons,List.length_cons,ih]; omega
private lemma pressing_ {X:Type*}[Monoid X] (w:Bool→ X)(n:ℕ): ((beats n).map w).prod=(w true*w false)^n:= by induction n with|zero=>simp[beats]|succ n ih=>simp [beats, ih,pow_succ',mul_assoc]

lemma travelling {Q:Choir}{C:Sequence}{P:Calibration C}{φ:ℕ→ℕ}(hQ:Q.Harmony P φ) (T:Pollens P Q) (A:EuPin→* (Q.W≃ₗ[ℂ] Q.W))(L: Ortho.Skew→ Q.W→ₗ[ℂ] Q.W) {β ε:ℝ} (h:C.Path β ε)(hP:P.System)(hφ:Tendsto φ atTop atTop) {I:Type*} [Fintype I]{m:ℕ} {u:ℝ} (z:I→ℂ) (w:I→List Bond)(hw: ∀ i, Strip.distinct (position (Q:=Q) (w i))) {σ:ℝ} (V:Chamber (F:=equip T A L) Q.total timeAxis)(B:Spread V) (H:Steady V)(E:Massive.Fields.Euclidean (F:=equip T A L) Q.total)(hr:Involutive (T.adj timeAxis))(hp:Available P φ w z u σ m)(hW:∀ i:I,Worn C φ (w i))(hs:0<σ)(hn: 0 ≤ u)(D:Panes B.algebra)(hd:D.Shines (dome V) B.algebra.subtype V.omega0)(t:B.algebra→⋆ₐ[ℂ]ℂ) : ‖t (Alk T A L z w hw V B)‖≤ u:=by
        obtain ⟨x,rfl⟩:=hd.onto.2 t; haveI:= hd.normalized; haveI:=hd.support; let Q:=Alk T A L z w hw V B
        apply exponent D.μ (fun x=> D.character x Q) (hd.weak _) hn _ x; intro n
        let K:=(beats n).length; let a:= aura T A L V B; let y:=beats n
        let s:Fin K→Bool:=List.get y; let X:= (List.ofFn fun i=> a (s i) Q).prod; have he:X=(star Q*Q)^n:=by
              have hZ:= pressing_ (fun i:Bool=> a i Q) n
              change (List.ofFn ((fun i: Bool=> a i Q) ∘ List.get y)).prod=_; rw [← List.map_ofFn,List.ofFn_get]; exact hZ
        -- D ground
        have hV(x:D.X): D.character x X=((↑((‖D.character x Q‖^2)^n)):ℂ):=by
              rw [he,map_pow,map_mul,map_star]; change (starRingEnd ℂ _*_)^n=_; rw[mul_comm,Complex.mul_conj,Complex.normSq_eq_norm_sq,Complex.ofReal_pow]; push_cast <;> rfl
        let E'(x:D.X):=(‖D.character x Q‖^2)^n; let x':ℝ:=∫x,E' x ∂ D.μ
        have hT:= hd.ground X; simp_rw [hV,integral_complex_ofReal] at hT; have he' :↑x'=inner ℂ V.omega0 (X.val V.omega0):=hT; have hv:=awake hQ T A L h hP hφ z w hw s V B H E hr hp hW hs; change ‖inner ℂ V.omega0 (X.val V.omega0)‖≤_ at hv; rw [← he',Complex.norm_real, Real.norm_of_nonneg (show 0 ≤ x' from integral_nonneg (fun i=>pow_nonneg (sq_nonneg _) _))] at hv; change x'≤_; exact hv.trans_eq (by unfold K; rw [beating])
lemma court {Q:Choir}{C:Sequence}{P:Calibration C}{φ:ℕ→ℕ}(hQ:Q.Harmony P φ) (T:Pollens P Q) (A:EuPin→* (Q.W≃ₗ[ℂ] Q.W))(L: Ortho.Skew→ Q.W→ₗ[ℂ] Q.W) {β ε:ℝ} (h:C.Path β ε)(hP:P.System)(hφ:Tendsto φ atTop atTop) {I:Type*} [Fintype I]{m:ℕ} {u:ℝ} (z:I→ℂ) (w:I→List Bond)(hw: ∀ i, Strip.distinct (position (Q:=Q) (w i))) {σ:ℝ} (V:Chamber (F:=equip T A L) Q.total timeAxis)(B:Spread V) (H:Steady V)(E:Massive.Fields.Euclidean (F:=equip T A L) Q.total)(hr:Involutive (T.adj timeAxis))(hp:Available P φ w z u σ m)(hW:∀ i:I,Worn C φ (w i))(hs:0<σ)(hn: 0 ≤ u)(D:Panes B.algebra)(hd:D.Shines (dome V) B.algebra.subtype V.omega0)(t:B.algebra→⋆ₐ[ℂ]ℂ) : ‖∑ j:I,z j * pointMoment (bloom B H t) (F:=equip T A L) (position (Q:=Q) (w j))‖ ≤ u:=by
        apply le_trans (Eq.le ?_) (travelling hQ T A L h hP hφ z w hw V B H E hr hp hW hs hn D hd t); congr 1; unfold Alk; rw [map_sum]; exact Finset.sum_congr rfl fun i _=>by rw[Bridge.Kly.bless B H t _ (show Fields.distinct (F:=equip T A L) (position (Q:=Q) (w i)) from hw i)]; exact (t.toAlgHom.toLinearMap.map_smul (z i) (M B (position (Q:=Q) (w i)) (hw i))).symm
end YM.Plata
#print axioms YM.Plata.travelling
#print axioms YM.Plata.court
