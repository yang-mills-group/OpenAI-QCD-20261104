import YM.Mural.Flora
import YM.Mural.Tall
import YM.Mural.Ewer
/-! # New reader with inheritance of capped spin letters. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Mural
open Function MeasureTheory Finset NormedSpace Creek Creek.Ledge Grass Matrix Cove Send Anomaly Filter
open scoped Topology BigOperators ContDiff Classical
variable {A B D:Type*}[Fintype A][Fintype B] (L:Alg A →L[ℂ] Alg B)
variable (f:A→ℝ)(g:B→ℝ){z b:ℝ}(n:ℕ)(X:Finset A)
lemma sail_in {x:Alg A} (h:1≤b)(hp:∀ i,0<f i)(hg:∀ i,0<g i) (hv:Mild L) (hh:∀ i∈region X, load g (L i) ≤ z*load f i) (hz:0≤z)(hx:x∈region X): repay univ b n g (L x)≤ z*repay univ b n f x:=by
    let P (i:Finset A):= premium univ b n i
    have hp' (s:Finset A)(he:s⊆X): repay univ b n g (L (mono s))≤ P s*load g (L (mono s)):=by
         let y:=L (mono s); rw [sheet _ _ _ g h hg,dry g hg (L (mono s)),mul_sum]; apply sum_le_sum; intro j _; by_cases hm:coef j y=0
         · change _*‖coef j y‖*_ ≤ _*(_* ‖coef j y‖); rw [hm,norm_zero]; simp
         rw [ticket_mono g j hg]; have h: premium univ b n j ≤ P s:= by
              have hk:= Rim.rimIn (hv s.card _ (Rim.layerIn (subset_univ _) le_rfl)) j hm; unfold P premium; simp only [inter_univ]; exact pow_le_pow_right₀ h (min_le_min le_rfl hk.2)
         calc _ ≤ P s*‖coef j y‖* ∏ i∈j,g i:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h (norm_nonneg _)) (prod_nonneg fun i _=>(hg i).le)
              _=P s*(_*‖coef j y‖):=by ring
    conv_lhs=> rw [←write x,map_sum];
    rw [sheet _ _ _ f h hp,mul_sum]; refine (repay_sum ..).trans (sum_le_sum fun i _=>?_) -- rewrite picks f x
    by_cases he:coef i x=0
    · rw [he,zero_smul,map_zero,Mural.repay_nil,norm_zero]; simp
    rw [map_smul,repayL]; have hX:= Rim.whenever x hx he; refine (mul_le_mul_of_nonneg_left ((hp' i hX).trans (mul_le_mul_of_nonneg_left (hh _ (Creek.regionMon hX (Rim.monoIn i))) (premNN _ _ _ h))) (norm_nonneg _)).trans_eq ?_; unfold P; ring
open RG Lattice Wilson QCD.Jets Kit Lat YM.Next.Free MassiveQCD.Stitch MassiveQCD.Ribbon Tablet Fj
variable {I E J:Type}[Fintype I]{c f:Side}{N:ℕ}{R:Rise f N E J}
local notation "A" => Modes f N
local notation "B" => Modes c N
variable (Y:Tablet R I) {Q:Ratio c f}{l:ℝ}{D:Type}(G:Send Q N D) (b:ℝ) (p:E→ℝ)(q:J→ℝ)(h:ℝ)
structure Firm (t:ℝ):Prop where
   pos :0 ≤ p
   non :0 ≤ q
   ready i x: premiumE f N I h b n (Y.read t x i)≤p i
   fees i x: premiumE f N I h b n (Y.plug i x)≤ q i
variable {X:Fj D E J→Support c}{t r θ:ℝ}{m:D→ℝ} (hp:Peak G t h θ r m) (hw:∀ U:Grid f,∀ s:Finset (Fj D E J), Mild (Tablet.tunnel G s U)) {o:I→Site f}{κ:I→Bool}(hf:Y.Flora t κ o)(hg:Firm n Y b p q h t)(hv:1 ≤ b)
include hf hw hp hg hv
lemma new_wage (s:Finset (Fj D E J))(U:Grid f)(he:Further.ShellBirth49.Fusing.Collide.spark X s): premiumE c N I θ b n (Y.hue t G s U) ≤ jewel G R X m p q r s:=by
    have hZ:∀ i:Keys f N⊕Spine I,0 < Tablet.chip h _ _ i:=by rintro (i|i); exact hp.bud; exact one_pos
    have hp': Coins Y p q h t:=⟨hg.pos,hg.non,fun i U=>(minor _ _ _ _ hv hZ _).trans (hg.ready i U),fun i U=>(minor _ _ _ _ hv hZ _).trans (hg.fees i U)⟩
    unfold Cove.jewel; split
    next ht=>
      unfold Tablet.hue; split
      next hv'=>
         let x:=Y.made t U s; let z:=burst κ (Y.markers s); let y:=scrape (Keys f N) z x.val; obtain ⟨hM,hP⟩:= lights_col Y G hf s U; have hf':Polite κ (Y.markers s) (Y.dye t G s U):= politeStep _ hM rfl
         have hφ: premiumE f N I h b n x≤ (∏ i∈leftE s, (Real.exp (p i) -1)) * ∏ i∈spent s,q i:=by
                  let Q:=leftKeys (Keys f N) (Spine I); let c:=Tablet.chip h (Keys f N) (Spine I); have he:= Mural.funded Q b n c hv hZ (leftE s) (fun i=>exp (Y.read t U i)-1) _ fun i _=>spicy Q b n c hv hZ _ _ (hg.ready i U)
                  unfold x premiumE Tablet.made; rw [map_mul]; exact (repay_prod _ _ _ _ hv hZ ..).trans (mul_le_mul he (Mural.funded _ b n c hv hZ (spent s) _ _ fun i _=>hg.fees i U) (repay_pos ..) ((repay_pos ..).trans he))
         rw [attachedM c N I θ b n hp.cup _ hf',show scrape (Keys c N) z (Y.dye t G s U).val= tunnel G s U y from wing ..]; apply le_trans (sail_in (tunnel G s U) (fun _=>h) (fun _=>θ) n (limits (coreW G R s)) hv (fun _=>hp.bud) (fun _=>hp.cup) (hw U s) _ _ (hP z))
         · rw [show (r^(kappa (G.trim+1) N * invSize R s))*(∏ i∈ops s,m i)*repay _ _ _ _ y = _ from mul_assoc ..,← attachedM _ _ I _ _ _ hp.bud _ hM]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hφ (prod_nonneg fun i _=>(hp.spare i U).nn)) (pow_nonneg (zero_le_one.trans hp.post) _)
         · intro i hi; exact (remitFee G hp s U hv'.2 i hi).trans_eq (mul_assoc ..|>.symm)
         · exact mul_nonneg (pow_nonneg (zero_le_one.trans hp.post) _) (prod_nonneg fun i _=> (hp.spare i U).nn)
      unfold premiumE; rw [map_zero,repay_nil]; exact mul_nonneg (pow_nonneg (zero_le_one.trans hp.post) _) (mul_nonneg (prod_nonneg fun i _=>(hp.spare i U).nn) (mul_nonneg (prod_nonneg fun i _=> sub_nonneg.mpr (Real.one_le_exp (hg.pos i))) (prod_nonneg fun i _=> hg.non i)))
    next hj=>
      push Not at hj
      obtain ⟨h1,h2⟩:=hj he; unfold Tablet.hue; split
      · unfold premiumE; rw [show light _ (Tablet.dye Y t G s U) = 0 from ?_,repay_nil]
        have hs:= he.1; have hp:(ops s).Nonempty:=by
           have hv:=pinch s; rw [h1,h2] at hv; rw [←hv] at hs; obtain ⟨w,hw⟩:=hs; unfold Fj.pin at hw; cases w
           next i=> exact ⟨i,by simpa using hw⟩
           next i=> rcases i with v|v <;> simp at hw
        have hk: axle G U s 1=0:=by
          unfold Cove.axle; obtain ⟨i,hi⟩:=hp; rw [← noncommProd_erase_mul _ hi,mul_apply_eq_comp,show bucks G _ U 1=0 from G.fuel U _,map_zero]
        change carry (Spine I) _ _=_; rw [show Tablet.made Y t U s=1 from by unfold Tablet.made; rw [h1,h2,prod_empty,prod_empty,mul_one],show (1:Tine f N I).val=stake (Keys f N) ∅ 1 from (Eq.trans (quiet ..) (map_one _)).symm,speaks]; rw [show tunnel G s U 1=0 from ?_,map_zero]; change wipe A B _ (axle G U s (near _ _ 1))=0; rw [map_one,hk,map_zero]
      unfold premiumE; rw [map_zero,repay_nil]
end YM.QCD.Mural
#print axioms YM.QCD.Mural.new_wage
