import YM.Oriole.Pike
/-! Metal.D linear pivot at introduction q. all approximations through smoky Curvature aperture. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Oriole
open QCD QCD.Lat QCD.Grass Lattice TensorProduct Function UV PCAC Filter MeasureTheory RG
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator ContDiff Classical TensorProduct
variable {d n:ℕ}(a b:Flavor 6)(g:Bool){c:Side}
open Poised.Display Poised.Stative Module Finset Revolve SourceRead Patria TorusPCAC.Geometry Cylinder QCD.Entr.Goals
local notation "T"=> Lat.Fiber
local notation "G"=> pulp g
local notation "A"=> wave (claw g 0)
local notation "C"=> wave (pulp g)
local notation "V"=> wave (gamma 0)
local notation "P5"=>wave Lat.g5
local notation "I"=> (0:Multi 8)
local notation "L"=> UV.first 0
open TorusPCAC.Ward Grass.Ward
variable (H:TaperHol)(F:Taper)(h η:ℝ)(Q:Sheet c)
lemma coil(H:Taper) (h:Globe.Tempo Q)(i:Axis) : Rv H i Q= P5* star (Rod c H i Q)* P5:=by
      have ht (p q:Site c): QCD.Run.cell Q p q=P5*star (QCD.Run.cell Q q p)*P5:=by
           nth_rw 1[← h.song]; rw [newborn,aura,chirality,onSpin,QCD.Bay.cell_ride_right,QCD.Bay.cell_ride_left,Equiv.refl_apply,Equiv.refl_apply,show QCD.Run.cell (star Q) p q=star (QCD.Run.cell Q q p) from QCD.Run.cell_flip ..,wave_star,g5_star] -- need qualify below
      change (∑ p:Site c,_)= _*star (∑ p:Site c,_)*_; rw[star_sum,Matrix.mul_sum,Matrix.sum_mul]; exact sum_congr rfl fun p _=>by
           rw [ht p 0,star_smul,Matrix.mul_smul,Matrix.smul_mul]; unfold Nw; rw[star_mul',Oriole.spark]; simp [SourceRead.profile]
lemma W_unit(M:Spike)(h:M∈unitary Spike): wave M∈unitary Bundle:=by constructor <;> first|rw [wave_star,wave_mul,h.1,wave_one]|rw [wave_star,wave_mul,h.2,wave_one]
lemma primeU(Y:Bundle)(hy:Y∈unitary Bundle): ‖Y‖=1:= CStarRing.norm_of_mem_unitary hy -- inspect
lemma anton (h:Globe.Tempo Q)(hV: ‖Rod c F 0 Q - V‖≤ η): ‖Rv F 0 Q+ V‖≤η :=by
     rw [coil Q F h 0]; let S:= P5; have he: S*star V*S= -V:=by rw [wave_star,gamma_star,wave_mul,wave_mul]; rw [show Lat.g5 * gamma 0 * Lat.g5= -gamma 0 from ?_,QCD.Revolve.wave_neg]; rw [mul_assoc,Lat.five, mul_neg, ← mul_assoc, g5_sq, one_mul]
     have hp: ‖S‖=1:= primeU S (W_unit Lat.g5 ⟨by simp,by simp⟩);
     change ‖S * _ * S + V‖ ≤ _; rw [show S *_ *S+ V=S*star (Rod c F 0 Q - V)*S from (by rw [star_sub,mul_sub,sub_mul,he,sub_neg_eq_add])]; apply (norm_mul_le ..).trans; rw [hp,mul_one]; exact (norm_mul_le ..).trans ((le_of_eq (by rw [hp, norm_star,one_mul])).trans hV)
-- expense for each sign
variable (q b₀ c₀:ℂ)(P Y:Density c 6)(X:Label 8)(hX:X=q • flame a b g 8 (by decide)+ b₀ • arbor a b g true+c₀ • arbor a b g false)(s:Bool)(hB:Plus (P 1))(hY:Y 1= PCAC.ore (0:Site c) s a b (pulp g) (P 1)) (hT:Tally H 0 X P Y)
noncomputable abbrev idealR (s:Bool)(g:Bool):ℂ:=if s then poli g else 1
noncomputable abbrev parL (s:Bool)(g:Bool):ℂ:= if s then 0 else idealR s g
noncomputable abbrev parR (s:Bool)(g:Bool):ℂ:= if s then idealR s g else 0
include hX hB hY hT
lemma truss (M:Sheet c) (hM:M= rayC P (if s then b else a))(hp:Globe.Tempo M)(hZ:‖Rod c H.T 0 M-V‖ ≤ η): ‖b₀-parL s g‖ + ‖c₀-parR s g‖ ≤ η:=by
      obtain ⟨hu,hv⟩:= deepR a b g H q b₀ c₀ X P Y s hB hY hT hX
      have hP: ‖A‖=1:= primeU A (W_unit _ (claw_unit ..)); have h':‖C‖=1:= primeU C (W_unit _ (P_high _)); have hA:A ≠ 0:=by intro h; rw [h,norm_zero] at hP; norm_num at hP
      cases s
      · change M=rayC P a at hM; simp only [Bool.false_eq_true,↓reduceIte] at hu; rw [← hM] at hu -- hp hZ don't contain
        change b₀ • A= - _ at hu; change c₀ • A=0 at hv; simp only [parR,parL,idealR,Bool.false_eq_true,↓reduceIte,(smul_eq_zero.mp hv).resolve_right hA,sub_zero,norm_zero,add_zero]; rw[show ‖b₀-1‖= ‖(b₀-1) • A‖ from by rw [norm_smul,hP,mul_one], sub_smul,one_smul,hu, show A=V*C from (wave_mul ..).symm]; -- error after axes reducible
        rw[show _ - V*C= -((Rv H.T 0 M + V)*C) from (by rw [add_mul]; abel),norm_neg]; apply (norm_mul_le ..).trans; rw[h',mul_one]; exact anton H.T _ M hp hZ
      · change M=rayC P b at hM; rw [← hM] at hu
        change c₀ • A= - _ at hu; change b₀ • A=0 at hv; simp only [parL, parR,idealR, ↓reduceIte,(smul_eq_zero.mp hv).resolve_right hA,sub_zero,norm_zero,zero_add]; rw [show ‖c₀-_‖ = ‖(c₀-poli g) • A‖ from by rw [norm_smul,hP,mul_one], sub_smul,hu]
        have ht:poli g • A= -(C*V):=by
          rw [wave_mul]; cases g
          · simp [pulp,claw,poli]
          change (1:ℂ) • _=_; rw [one_smul]; change wave (gamma 0*g5)= -(wave (g5*gamma 0)); rw[Lat.five,QCD.Revolve.wave_neg]
        rw [ht,show - (C * _) - -(C*V)= -(C* (Rod c H.T 0 M-V)) from (by rw [mul_sub]; abel), norm_neg]; apply (norm_mul_le ..).trans; rw [h',one_mul]; exact hZ
end YM.Massive.Oriole
#print axioms YM.Massive.Oriole.truss
