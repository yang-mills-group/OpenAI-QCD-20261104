import YM.QCD.Stew.Reine
/-! # rotation and gamma-5 of the jet stencil at all fields -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Stew
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N:ℕ} {v:Strut c}{k:Spike}{g:Site c→ℂ}
open Revolve Flume Quarry AnalyticBridge.VerifiedReset
lemma principal (o:Site c)(M:Spike)(hp: Warrant v g k): localX o M * haze v k g=haze v k g * localX (act v o) (k*M*star k):=by
    change localX o M*rides (act v) _=rides (act v) _*_; unfold localX; rw [ride_mul,ride_mul,Equiv.refl_trans,Equiv.trans_refl]; apply congr_arg; funext i; change _ *lightP v k g i=lightP v k g i* _; unfold lightP; by_cases ht:i=o
    · simp only [ht, ↓reduceIte,Matrix.mul_smul,Matrix.smul_mul,wave_mul]; congr 2; simp only [← Matrix.mul_assoc,hp.2.unit.1,one_mul]
    rw [if_neg (Ne.symm ht), if_neg ((act v).injective.ne (Ne.symm ht)),zero_mul,mul_zero]
lemma pineS (o:Site c)(M:Spike)(d:ℂ) :localX o (d • M)=d • localX o M:=by unfold localX; rw [ride_smul]; refine congr_arg _ (funext fun i=> ?_); dsimp only [Pi.smul_apply]; split; exact Matrix.smul_kronecker ..; exact (smul_zero _).symm
lemma freshE (o:Site c)(M: Spike)(s:SampleX)(U:Grid c)(hp: Warrant v g k):entry o M s (sky v U)*haze v k g=haze v k g*entry (act v o) (skySig v.1 s • (k*M*star k)) (tide v.1 s) U:=by
    let A:=haze v k g; let q:=act v o; let Y:=k*M*star k
    rcases s with _|⟨a,_|_⟩
    · simp only [entry, tide,Equiv.optionCongr_apply, Option.map_none,skySig, Option.elim, one_smul]; exact principal o M hp
    · let d:=skySig v.1 (some (a,true))
      change -delta (sky v U) a*localX o M * A=A*(-delta U _ *localX q (d • Y)); rw [Matrix.mul_assoc, principal o M hp, ← Matrix.mul_assoc, Matrix.neg_mul,show delta _ a*A =_ from Δ_comm o a hp U, pineS,Matrix.mul_smul,Matrix.mul_smul]; -- sign
      simp only [d,q,A,Y,neg_smul,smul_neg, Matrix.neg_mul, Matrix.mul_neg, Matrix.smul_mul, Matrix.mul_assoc]
      rfl
    change localX o M*delta (sky v U) a*A=A*(localX q (_ • Y) *delta U _); rw [Matrix.mul_assoc,show delta _ _*A=_ from Δ_comm o a hp U,Matrix.mul_smul, ← Matrix.mul_assoc (localX o M), principal o M hp,Matrix.mul_assoc, pineS,Matrix.smul_mul,Matrix.mul_smul]; rfl
lemma rentsL (o:Site c)(M:Spike)(R:Spike): onSpin c R*localX o M=localX o (R*M):=by unfold onSpin localX; rw [ride_mul]; apply congr_arg₂ rides rfl; funext i; simp only [Equiv.refl_apply]; split<;> first| exact wave_mul .. | exact mul_zero _
lemma rent_rev (o:Site c)(M:Spike)(R:Spike): localX o M*onSpin c R=localX o (M*R):=by unfold onSpin localX; rw [ride_mul]; apply congr_arg₂ rides rfl; funext i; split <;> first| exact wave_mul ..| exact zero_mul _
lemma Δ_spins (U:Grid c)(i:Axis)(M:Spike): Commute (delta U i) (onSpin c M) := (((shift_spin M (0:Site c) U i).sub_left (back_spin M 0 _ _))).smul_left _ -- back_spin order
lemma tiltE (o: Site c)(M: Spike)(p:SampleX)(U:Grid c): entry o (g5*star M*g5) (invert p) U =chirality c *star (entry o M p U)*chirality c:=by
   rcases p with _|⟨q,_|_⟩
   · change localX o _=chirality c *star (localX o M)* _; rw [localStar]; unfold chirality; rw [rentsL,rent_rev]
   · change localX o _ *delta U q= _*star (-delta U q*localX o M)*_; rw [star_mul, star_neg, localStar,δ_back]; unfold chirality; rw [neg_neg,← Matrix.mul_assoc, rentsL, Matrix.mul_assoc (localX o _), (Δ_spins ..).eq,← Matrix.mul_assoc,rent_rev]
   change -delta U q *localX o _= _*star (localX o M* delta U q)*_; rw [star_mul,δ_back,localStar]; unfold chirality; rw [← Matrix.mul_assoc,Matrix.mul_neg,← (Δ_spins ..).eq,← Matrix.neg_mul _, Matrix.mul_assoc (- delta U q) (onSpin c g5), rentsL,Matrix.mul_assoc (- delta U q),rent_rev]
lemma gate_delta (U: Grid c)(t:Axis)(g: Frame c): delta (gauge g U) t*siteRot g=siteRot g* delta U t:=by
    let Z:= siteRot g
    unfold delta; simp only [Matrix.smul_mul, Matrix.mul_smul, sub_mul,mul_sub]; apply congr_arg; apply congr_arg₂ (·-·)
    · rw [Lat.site_transform]; simp only [Matrix.mul_assoc,(siteRot_u g).1,mul_one]
    rw [Lat.site_transform]; simp only [star_mul,star_star,Matrix.mul_assoc,(siteRot_u g).1,mul_one]
lemma commG (o:Site c)(p:Spike)(g:Frame c):Commute (siteRot g) (localX o p):=by change siteRot g*_=_; unfold siteRot localX; rw [ride_mul,ride_mul]; apply congr_arg; funext i; simp only [Equiv.refl_apply]; split; exact (interlace ..).eq; simp
lemma gateE (o: Site c)(M:Spike)(q:SampleX)(V:Grid c)(g: Frame c): entry o M q (gauge g V)*siteRot g=siteRot g*entry o M q V:=by
    rcases q with _|⟨a,_|_⟩; · exact (commG ..).symm.eq
    · change (-delta _ a*localX o M)*_= _ *(-delta _ a*_); rw [Matrix.mul_assoc,← (commG ..).eq, ← Matrix.mul_assoc,Matrix.neg_mul,gate_delta, ← Matrix.mul_neg _, Matrix.mul_assoc] -- ←mul_neg proof? check
    change localX o M*delta _ a*_=_*( _*delta _ a); rw [Matrix.mul_assoc,gate_delta,← Matrix.mul_assoc,←(commG ..).eq,Matrix.mul_assoc]
end YM.QCD.Stew
