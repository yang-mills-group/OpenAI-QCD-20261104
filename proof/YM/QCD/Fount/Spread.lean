import YM.QCD.Fount.Cut
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Fount
open Lat Kit Lattice Wilson Function Finset Filter Metric Tree RG Precision Bloch Laurent
open Orbit Flume Sparks Quarry Stationary YM.Next.Free Pine Eyrie Revolve Rudder
open Extra Iteration Placement QCD.Run Work.F08 Work.F03 Exterior Garden Leaf Tee LeafM
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator ContDiff Classical
variable {j k N:ℕ}{t p b C:ℝ}{P:Flight j k}{f c:Side}{e:f.val=c.val*P.L.val}
abbrev stone : Bloom 0:=⟨[],Fin.elim0,fun _=>1⟩
lemma beamQ : stone.Spins:=by
    intro d x; have he: touch (colour d)∈unitary _:= by apply touch_u; exact ⟨su.mat_star_mul _,su.mat_mul_star _⟩
    have h(v: Fin 0→su.Color):stone.hues v=1:=by unfold stone Bloom.hues; simp
    rw [h,h,mul_one]; exact he.2.symm
lemma litho : epilogue stone (0:Cnr f)=1:=by
    ext ⟨x,i⟩ ⟨y,j⟩; change cell (epilogue stone _) x y i j=_; rw [whereRay]
    have he:stop (0:Cover) stone.tail=0:=rfl; rw [he]; simp only [map_zero, add_zero]
    by_cases hp:x=y
    · subst y; simp only [if_true]
      have hc:occ x 0=1:=by
         have ht:=concord (0:Site f) x 0; rw [map_zero,add_zero,mode_zero,mul_one] at ht
         exact (mul_eq_right₀ (scarf_ne _ x)).1 ht -- inspect
      have ht:lepton stone (0:Cnr f) x=1:=by unfold lepton Bloom.hues stone; simp
      rw [hc,one_smul,ht]; simp [Matrix.one_apply]
    rw [if_neg hp]; simp [Matrix.one_apply,hp]
abbrev padL (L:Side):Columns L:=fun _=>0
lemma paddedP (L:Side)(hp:0 ≤ p):(padL L none).strip p 0 :=by intro i j; refine ⟨fun x=>by positivity,Summable.of_norm ?_,?_⟩ <;> simp [padL]
abbrev priorP : Unit → Bloom 0 := fun _ => stone
abbrev driftP (P:Flight j k) := tray P (padL P.L) priorP
lemma stoneB (hp:0 ≤ p):Fractal priorP p (stone.paid p) :=by refine ⟨hp,fun _=>beamQ,Summable.of_finite,by simp [priorP]⟩
lemma portend (hj:4≤j)(hk:4≤k):∃ a A:ℝ,0<a ∧ 0≤A ∧ ∀ P:Flight j k, Fractal (driftP P) a (A*(P.L.val:ℝ)):=by
   obtain ⟨t,C,h,hC,H⟩:=pack_funds hj hk; let C' := bouquet C 0 t 0*stone.paid t; have hc':0≤C':=mul_nonneg (by unfold bouquet; positivity) (frc ..)
   refine ⟨t,C',h,hc',fun P=>?_⟩; let L:ℝ:= P.L.val; let b:=C*slope P.L/L; let D:= bouquet b 0 t 0
   have hv:0<L:= side_pos _; have hb:0≤ b:=by unfold b; have h:=slope_pos P.L; positivity
   have hv':t ≤ t*L:=le_mul_of_one_le_right h.le (by unfold L; exact_mod_cast P.L.property)
   have hh : (Fintype.card (Site P.L):ℝ)*(D*stone.paid t)=C'*L:=by
       have hz:slope P.L^2=L⁻¹:=by rw [Kit.slope, inv_pow,Real.sq_sqrt hv.le]
       unfold C' D bouquet b; rw [site_card,Nat.cast_pow]; change L^4*_=_
       unfold L at *; ring_nf at *; field_simp at hz; field_simp; linear_combination C^2*stone.paid t * hz
   have he : SumBudget (fun i=> (driftP P i).paid t) (C'*L):=by
      rw [← hh]; let I:= Site P.L
      have hI i: SumBudget (fun j=>(jar P _ stone i j).paid t) (D*stone.paid t):= tray_price stone i h.le hv' hb (show 0≤(0:ℝ) by norm_num) (fun i=>(H P i).1) (by simpa only [Nat.cast_zero,add_zero,mul_one] using (H P i).2) (paddedP _ h.le)
      have hD:0≤D*stone.paid t:=Iteration.Cost.nonneg (hI 0)
      refine Iteration.Cost.product (f:=fun _=>(Fintype.card I:ℝ)*(D*stone.paid t)) ?_ (fun _=>?_)
      swap
      · exact Iteration.Cost.product (Iteration.Cost.finite _ hD) hI
      simpa only [Fintype.card_unit,Nat.cast_one,one_mul] using! (Iteration.Cost.finite (α:=Unit) ((Fintype.card I:ℝ)*(D*stone.paid t)) (by positivity))
      -- params
   exact ⟨h.le,fun i=> jar_spin _ _ _ _ beamQ _, he.2.1,he.2.2⟩
end YM.QCD.Fount
