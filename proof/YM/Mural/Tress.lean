import YM.Next.STATIONARY.FrameEst.Center
import YM.Mural.Foll
/-! # Uniform entrywise accounting of coarse strips and clock fluctuation
The volume cutoff for each block may be imposed after clocks: offset injection. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Comet
open QCD QCD.Grass QCD.Finch QCD.Lat Lattice Wilson RG
open Function Finset MeasureTheory Filter Fork Laurent Flume Kit Pine
open scoped ContDiff BigOperators Matrix Matrix.Norms.L2Operator Classical Kronecker
open YM.Next.Free
variable {c f:Side}{j k m:ℕ} (P:Flight j k)(d:f.val=c.val*P.L.val)(t:Site f) (x:Site c)(y:Site f)
local notation "S"=> sliceL P d
local notation "Iy"=> P.patch.Points
set_option quotPrecheck false
local notation "M"=> arctic P.L j
local notation "Xg"=> (sliceL P d).embed x
local notation "Ty"=>texel P d t x y
variable (U:Grid f)(w:Walk)
variable (hp: 2*P.patch.radius < f.val)
lemma observe (a:Lattice.Order)(i k:Iy)(hv:stop Xg (route 0 i.val a)=stop Xg (route 0 k.val a)) (hp:2*P.patch.radius < f.val) : i=k:=by
   rw [wrap_stop,wrap_stop Xg,route_end,route_end] at hv
   have hz (w:Iy)(x:Axis) : -(f.val:ℤ)< 2*(w.val x)∧ 2*(w.val x) ≤ f.val:= by obtain ⟨hm,h⟩:=box_test.mp w.property; have ht:=hm x; have hv:=h x; omega
   exact Subtype.ext (Lattice.wrap_injOn f (hz i) (hz k) (add_left_cancel hv))
lemma shadeC (g:su.El): ‖colour g‖≤1:= rotation_price ⟨su.mat_star_mul _,su.mat_mul_star _⟩
lemma modelB (o:Site f)(w:Walk): ‖turn t U w o‖ ≤ 1:=by unfold turn; rw [norm_smul,nPrice, one_mul]; exact shadeC _
-- express price $= sqrt inverse * L^-2 $
include hp
lemma entryL : ‖Ty U‖ ≤ Kit.scale P.L:=by
   let b:=byteV P d t x y; have he(a:Lattice.Order) : ‖b a U‖≤ ((P.L.val:ℝ)⁻¹)^4:=by
        by_cases hx: ∃ i:Iy, stop Xg (route 0 i.val a)=y
        · obtain ⟨i,hi⟩:=hx; unfold b byteV; rw [sum_eq_single i]; rotate_left
          · intro c _ hc; unfold edgeB; dsimp only; rw [if_neg (show stop _ _≠_ from fun h=>hc (observe P d x a c i (h.trans hi.symm) hp)),smul_zero]
          · simp
          unfold edgeB; dsimp only; rw [if_pos hi,norm_smul,Complex.norm_real,Real.norm_of_nonneg (P.patch.weight_nonneg _)]
          exact (mul_le_of_le_one_right (P.patch.weight_nonneg _) (modelB ..)).trans (YM.Stationary.Audience.salon_vote i)
        unfold b byteV; rw [sum_eq_zero (fun i _=>?_ ), norm_zero]; · positivity
        rw [edgeB,if_neg (fun h=>hx ⟨_,h⟩), smul_zero]
   let g:= (((P.L.val:ℝ))⁻¹)^4; let F:= (massL P.L:ℝ); rw [texel,norm_smul,Complex.norm_real, Real.norm_of_nonneg (mass_pos P.L).le, norm_smul,norm_inv, Complex.norm_natCast]
   have hm : ∑ _a:Lattice.Order, g=(votes:ℝ)*g:=by rw [sum_const,card_univ,nsmul_eq_mul]
   have hv: (massL P.L)*((votes:ℝ)⁻¹*((votes:ℝ)*g))=scale P.L:=by rw [← mul_assoc _ (votes:ℝ),inv_mul_cancel₀ Kit.poll_pos.ne',one_mul]; unfold massL g Kit.scale; field_simp
   rw [←hv]; apply mul_le_mul_of_nonneg_left _ (mass_pos _).le; exact mul_le_mul_of_nonneg_left ((norm_sum_le ..).trans ((sum_le_sum fun i _=>he i).trans_eq hm)) (by positivity)
omit hp
lemma dormant (h:M < separation Xg y) : Ty U=0:=by
    unfold texel; rw [sum_eq_zero (fun i _=>?_ ),smul_zero,smul_zero]; unfold byteV; apply sum_eq_zero; intro b _; unfold edgeB; dsimp only; rw [if_neg (fun hp=>?_ ),smul_zero]; exact not_lt_of_ge (((QCD.Eyrie.stopped _ Xg).trans (stems ..)): separation Xg (stop Xg (route 0 b.val i))≤ M) (show _ from hp.symm ▸ h)
lemma staffT (v: Lat.Frame f) : Ty (gauge v U)= colour (v Xg) * Ty U * star (colour (v y)):=by
    unfold texel byteV; simp only [Matrix.sum_mul,Matrix.mul_sum,Matrix.smul_mul,Matrix.mul_smul]; apply congr_arg; apply congr_arg; apply sum_congr rfl; intro a _; apply sum_congr rfl; intro i _; apply congr_arg; unfold edgeB; dsimp only; split; next hp=> unfold turn; rw [travel_gauge,colour_mul,colour_mul,colour_inv, hp,Matrix.mul_smul, Matrix.smul_mul ]
    next h=> simp
lemma respects (B:ℕ)(hp:M ≤ B): LocalOn (trunkFt Xg B) Ty:=by
    intro U V h; unfold texel byteV; apply congr_arg; apply congr_arg; apply sum_congr rfl; intro a _; apply sum_congr rfl; intro i _; apply congr_arg; unfold edgeB; dsimp only; split; swap; · rfl
    unfold turn; apply congr_arg; apply congr_arg; apply travel_local Xg
    exact agrees_mono h fun j hj=>halo_spec.mpr ⟨_,mem_singleton_self _, ((QCD.Eyrie.walked _ _ _ (show j∈visits Xg (route 0 i.val a) from hj)).trans (stems ..)).trans hp⟩
-- flat phase scalar
noncomputable def lightS:= Ty (1:Grid f) (0:Hue) (0:Hue)
lemma portrait : Ty 1=lightS P d t x y • (1:Mat):=by
   let D (X:Mat):Prop:=∃ b:ℂ,X=b•1
   have h1(z:ℂ)(x)(h:D x):D (z • x):=by obtain ⟨b,rfl⟩:=h; exact ⟨z*b,(mul_smul ..).symm⟩
   have h0 : D 0:=⟨0,(zero_smul ..).symm⟩
   have hs{A:Type}(s:Finset A)(f:A→ Mat)(h:∀ i,D (f i)):D (∑ i∈s,f i):=by choose b h using h; refine ⟨∑ i∈s,b i,?_⟩; simp_rw [h,sum_smul]
   have hu (i:Lattice.Order)(j:Iy):D (edgeB P d t x y j i 1):=by unfold edgeB; dsimp only; split; exact ⟨_,zedTurn ..⟩; exact h0
   obtain ⟨b,hb⟩:= h1 (massL P.L:ℂ) _ (h1 ((votes:ℂ)⁻¹) _ (hs univ _ (show ∀ i:Lattice.Order,D (byteV P d t x y i 1) from fun i=>hs univ _ (fun j=> h1 _ _ (hu i j)))))
   unfold lightS; rw [show Ty 1=b • 1 from hb]; simp
end YM.QCD.Comet
#print axioms YM.QCD.Comet.portrait
#print axioms YM.QCD.Comet.entryL
