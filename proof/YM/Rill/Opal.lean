import YM.Rill.Amen
/-! Power bounded slab operators including empty slab. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Tarn.Quilt
open YM.Analysis YM.Fir Fir Fir.Gains Fir.TagF Filter Set Metric
open Lattice Cells Lyre QCD QCD.Lat QCD.Tide QCD.Grass QCD.Plum QCD.RP QCD.Revolve UV Needle Patria Patria.Depth Patria.Hub Poised Plans Plans.Stamp Intag Intag.Vale Romance
open scoped Topology ContDiff BigOperators Classical ComplexOrder
open Function Sash TorusPCAC.Geometry Finset Goblet Choir Choir.Strip
variable {C:Sequence} {P:Calibration C} {n:ℕ} {Q:Choir}(L:Pollens P Q) (a:Axis)
variable (p:Strip Q)(d r:ℝ)(j:ℕ)(W:ℝ) (he:manor p a d r)(hr:0<r)(hd:0 ≤ d)
variable (G:∀ d,Cottage P d)(hS:Sway C.S) {β e:ℝ}(hp:C.Path β e) {φ:ℕ→ℕ} (H:Q.Harmony P φ)(hφ:Tendsto φ atTop atTop) (hP:P.System)
variable {v w:Strip Q}
include G hp H hφ hS
lemma eternally (hv:Sunny v a)(hw:Sunny w a): ∃ A:ℝ,0 ≤ A ∧∀ r:ℝ,0 ≤ r→ ‖Strip.reach L a v (echo a r w)‖ ≤ A:=by
     let B:=oppositeS L a v; obtain ⟨ℓ,hℓ,X,hX,h⟩:= Privilege.post L a G hS hp H hφ 1 ((B.length+w.length)*6+1) hv hw; refine ⟨X^(B.length+w.length),by positivity,fun r hr=>?_⟩; obtain ⟨ht,hH,hu⟩:=h r hr
     have hp:= plaza hp H hφ B [] (echo a r w) 0 ℓ 1 X (I:=Fin 0) 0 hℓ (by simp [(C.S.step 0).L.pos]) (by rw [echo_tape]; exact ht) (by simp[gap]) hu (fun _ _ _ hi=>List.not_mem_nil hi|>.elim) hH (fun _ hi=> List.not_mem_nil hi|>.elim)
     simpa only[List.append_nil,List.length_nil, echo_tape,pow_zero,mul_one] using hp
omit G hp H hφ hS
variable (X:Strip Q→Strip Q)
lemma glueSym (F: Strip Q→ Strip Q)(hl:∀ v,Sunny v a→ Sunny (F v) a)(hx:∀ v,Sunny v a→ Sunny (X v) a)(hp:∀ v w,Sunny v a→ Sunny w a→Strip.reach L a (X v) w=Strip.reach L a v (F w))(hq:∀ v w, Sunny v a→ Sunny w a→ Strip.reach L a (F v) w=Strip.reach L a v (X w)):∀ v w,Sunny v a→Sunny w a→Strip.reach L a ((F∘X) v) w= Strip.reach L a v ((F∘X) w):=fun v w hv hw=> (hq (X v) w (hx _ hv) hw).trans (hp v (X w) hv (hx _ hw))
lemma combining (Y:Strip Q→Strip Q) {B:ℝ}(hb:0≤B)(hQ:∀ v w,Sunny v a → Sunny w a → ∃ A:ℝ,0 ≤ A ∧∀ i:ℕ, ‖Strip.reach L a v (Y^[i] w)‖ ≤ A * B^i) (v:Fin n → Strip Q)(hV:∀ i,Sunny (v i) a)(u:Fin n→ℂ):∃ A:ℝ,0 ≤ A∧∀ i:ℕ, ‖valley L a v (Y^[i] ∘v) u u‖≤ A*B^i:=by
     choose p hp ht using fun i j:Fin n=>hQ (v i) (v j) (hV i) (hV j); let Z(i j:Fin n):ℝ:= ‖u i‖ *p i j * ‖u j‖; refine ⟨∑ i,∑ j,Z i j,sum_nonneg fun i _=>sum_nonneg fun j _=>?_,fun i=>?_⟩
     · exact mul_nonneg (mul_nonneg (norm_nonneg _) (hp _ _)) (norm_nonneg _)
     unfold valley; rw [sum_mul]; apply (norm_sum_le ..).trans; refine sum_le_sum fun k _=>?_ ; rw[sum_mul]; apply (norm_sum_le ..).trans; refine sum_le_sum fun j _=>?_; rw [norm_mul,norm_mul,norm_star]; exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (ht k j i) (norm_nonneg _)) (norm_nonneg _)).trans_eq (by unfold Z; ring)
lemma sunny_eq (v:ℂ)(hx:0 ≤ v): v= (↑‖v‖:ℂ):=by
     have h:= Complex.nonneg_iff.mp hx; have ht:v=(↑v.re:ℂ):=Complex.ext (by simp) h.2.symm; nth_rw 2 [ht]; rw [Complex.norm_real,Real.norm_of_nonneg h.1]; exact ht
include G hp H hφ hS hP
lemma mayor (Y:Strip Q→Strip Q)(hx:∀ v,Sunny v a→Sunny (X v) a)(hp':∀ v,Sunny v a→ Sunny (Y v) a)(hX:∀ v w,Sunny v a→ Sunny w a→Strip.reach L a (X v) (X w)= Strip.reach L a v (Y w))(hq:∀ v w,Sunny v a→ Sunny w a→ Strip.reach L a (Y v) w=Strip.reach L a v (Y w)) (A:ℝ)(ht:0<A)(hm:∀ v w,Sunny v a→ Sunny w a →∃ B:ℝ,0 ≤ B ∧∀ i:ℕ, ‖Strip.reach L a v (Y^[i] w)‖≤ B*A^i)(v:Fin n→Strip Q)(hV:∀ i,Sunny (v i) a)(u:Fin n→ℂ): crestG L a n (X ∘ v) u ≤ (A:ℂ)*crestG L a n v u:=by
     obtain ⟨B,hB,hc⟩:= combining L a Y ht.le hm v hV u; let K:= valley L a v v u u; let V:= X ∘ v; let S:= valley L a V V u u; have hp':=Strip.symmetry hP hφ L a hp G hS H hp' hq hV u hB ht hc; have hs':S=valley L a v (Y ∘ v) u u:= sum_congr rfl fun i _=> sum_congr rfl fun j _=> by rw[show Strip.reach L a (V i) (V j)= Strip.reach L a (v i) ((Y∘v) j) from hX _ _ (hV i) (hV j)] -- syntax
     change S ≤ _*K; nth_rw 1 [sunny_eq S (signal hP hφ L a hp G hS H _ _ fun i=> hx _ (hV i)), sunny_eq K (signal hP hφ L a hp G hS H _ _ hV)]; rw[← Complex.ofReal_mul]; rw [Complex.real_le_real]; rw [hs']; exact hp'
end YM.Massive.Tarn.Quilt
#print axioms YM.Massive.Tarn.Quilt.mayor
