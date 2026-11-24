import YM.QCD.Globe.Fox
import YM.QCD.Nola.Wheat
import YM.QCD.Nola.Arch
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Globe
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
open Revolve Villa Port Footprint AnalyticBridge.VerifiedReset Flume Pine YM.Next.Free Leaf LeafM Tee Garden Entr Kites
variable {f c:Side}{j k m N:ℕ}{S:Flight j k} {h:f.val=c.val*S.L.val}{p:BudgetPoint}
variable (S h) {a b t w:ℝ}
lemma shorter (r:Ratio c f)(x y:Site f):costS m (r.parent x) (r.parent y) ≤2^m*costS m x y:=by
    unfold costS; rw [←mul_pow]; apply pow_le_pow_left₀ (by positivity); have hp:r.count.val*(separation (r.parent x) (r.parent y)) ≤ separation x y+r.count.val:=Corona.foreshorten ..
    have he:(separation (r.parent x) (r.parent y))≤ separation x y+1:=by
                                                                                                      apply Nat.le_of_mul_le_mul_left _ r.count.property; rw [Nat.mul_add,Nat.mul_one]; exact hp.trans (Nat.add_le_add_right (Nat.le_mul_of_pos_left _ r.count.property) _)
    have hu:(separation (r.parent x) (r.parent y):ℝ) ≤ separation x y +1:=by exact_mod_cast he
    linarith [Nat.cast_nonneg (α:=ℝ) (separation x y)]
lemma overleaf {D E:Type*}[Fintype D][Fintype E](r:Ratio c f)(P:D→Site f)(Q:E→Site f)(X:ArrayL D E)(h:Cent P Q m a X): Cent (r.parent∘P) (r.parent∘Q) m (2^m*a) X:=by
    intro i; apply le_trans _ (mul_le_mul_of_nonneg_left (h i) (show 0≤(2:ℝ)^m by positivity)); unfold Gan; rw [mul_sum]; apply sum_le_sum; intro j _; rw [←mul_assoc]; exact mul_le_mul_of_nonneg_right (shorter ..) (norm_nonneg _)
lemma maple (r:Ratio c f)(X:Kit.Rail c c)(he: Ton r.embed r.embed m a X): Beam X m (2^m*a):=by
    have hp:r.parent ∘ r.embed=id:=funext fun i=>r.embed_parent i; exact ⟨by rw [←hp]; exact overleaf _ _ _ _ he.toR,by rw [←hp]; exact overleaf _ _ _ _ he.axR⟩
-- nonlinear ledger high.Plants at patch
set_option quotPrecheck false
local notation "R"=>sliceL S h
local notation "Q"=>tied S h 0 1
local notation "O"=> father S h
lemma aph (X Y:Sheet f)(hp:IsUnit X.det)(he: Beam X⁻¹ m a)(hv: Beam Y m b)(ha:0≤a)(hb:0≤b)(hz:a*b≤1/2): IsUnit (X+Y).det∧ Beam (X+Y)⁻¹ m (2*a):=by
    let A:= X⁻¹*Y; have hY: X+Y=X*(1+A):=by unfold A; rw [mul_add,mul_one,← mul_assoc, Matrix.mul_nonsing_inv _ hp, one_mul]
    have hA:Beam (1-(1+A)) m (a*b):=by rw [show 1 - (1+A)= -A by abel]; exact (he.op hv ha hb).neg
    have hd:0 < 1-a*b:=by linarith
    obtain ⟨hq,ht⟩:= hA.near (mul_nonneg ha hb) (by linarith)
    rw [hY, Matrix.det_mul,Matrix.mul_inv_rev]; have hm:(1-a*b)⁻¹ ≤2:= (inv_le_of_inv_le₀ (by norm_num) (by linarith : (2:ℝ)⁻¹ ≤ _)) -- name
    exact ⟨hp.mul hq,(ht.up hm).op he (by norm_num) ha⟩
lemma distIl {D E:Type*}[Fintype D][Fintype E][DecidableEq D][DecidableEq E](X Y: ArrayL D D) (A:ArrayL E D)(hp:IsUnit X.det)(h:IsUnit (X+Y).det): A*(X+Y)⁻¹=A*X⁻¹-A*X⁻¹*Y*(X+Y)⁻¹ ∧ (X+Y)⁻¹ * Aᴴ = X⁻¹*Aᴴ-(X+Y)⁻¹*Y*X⁻¹*Aᴴ∧
    1-A*(X+Y)⁻¹*Aᴴ=1-A*X⁻¹*Aᴴ + (A*X⁻¹*Y*(X⁻¹*Aᴴ) - A*X⁻¹*Y*(X+Y)⁻¹*Y*(X⁻¹*Aᴴ)):=by
    let M:=X+Y; let G:=(X+Y)⁻¹; let H:= X⁻¹
    have hh:G-H= -(H*Y*G):=by
         have he:H*(X-M)*G=G-H:=by rw [Matrix.mul_sub,Matrix.sub_mul, Matrix.nonsing_inv_mul _ hp, Matrix.one_mul,Matrix.mul_assoc,show M*G=1 from Matrix.mul_nonsing_inv _ h,Matrix.mul_one]
         rw [← he,show X-M= -Y by unfold M; abel]; simp
    have hr:G-H= -(G*Y*H):=by
         have he:G*(X-M)*H=G-H:=by rw [Matrix.mul_sub,Matrix.sub_mul,show G*M=1 from Matrix.nonsing_inv_mul _ h,Matrix.one_mul,Matrix.mul_assoc,Matrix.mul_nonsing_inv _ hp,Matrix.mul_one]
         rw [← he,show X-M= -Y by unfold M; abel]; simp
    have h1:A*G=A*H-A*H*Y*G:=by
          suffices he:A*G-A*H= -(A*H*Y*G) by rw [← sub_add_cancel (A*G) (A*H),he]; abel
          rw [← Matrix.mul_sub,hh,Matrix.mul_neg]; simp only [Matrix.mul_assoc]
    have h2:G*Aᴴ= H*Aᴴ-G*Y*H*Aᴴ:=by
          suffices he:G*Aᴴ-H*Aᴴ= -(G*Y*H*Aᴴ) by rw [← sub_add_cancel (G*Aᴴ) (H*Aᴴ),he]; abel
          rw [← Matrix.sub_mul,hr,Matrix.neg_mul]
    refine ⟨h1,h2,?_⟩; change 1-A*G*Aᴴ=1-A*H*Aᴴ+(_-A*H*Y*G*Y*(H*Aᴴ)); rw [h1, Matrix.sub_mul, sub_sub_eq_add_sub]; rw [Matrix.mul_assoc _ G,h2,Matrix.mul_sub]; simp only [Matrix.mul_assoc]; abel
lemma stern (P:Plan k)(K W μ:Sheet f)(hK: K=W+μ)(hy: Tempo K)(ha:0 ≤ a)(hb:0 ≤ b)(ht:0 ≤ t)(hz:0 ≤ w)(hF:IsUnit (O).det)(hc: Beam K m a)(hB: Beam W m b)(hp: Cent id id m t (barP S h*μ*proton S h)) (hG: Beam (O)⁻¹ m w)(hl: Ton (R).embed id m w (barP S h))(hr:Ton id (R).embed m w (proton S h))(hv:w*a ≤1/2)(G:Plan j):
    let A:=1-Q*((O)+K)⁻¹*(Q)ᴴ-sunny P S.land c
    Beam A m (2^m*(w^2*b)+ t+2^m*(2*w^3*a^2))∧ IsUnit ((O)+K).det ∧ Beam ((O)+K)⁻¹ m (2*w) ∧ Ton id (R).embed m (2*w^2*a) (((O)+K)⁻¹*(Q)ᴴ-proton S h) ∧ Tempo A:=by
    obtain ⟨hA,hH⟩:= aph _ _ hF hG hc hz ha hv; let V₀:=proton S h; let H' :=barP S h; let D:= ((O)+K)⁻¹; let Z:=1-Q*D*(Q)ᴴ; intro A; change Beam (Z- sunny P S.land c) _ _∧ _
    have he: IsUnit (O).det:=hF -- typo
    obtain ⟨hh,h',hX⟩:= distIl (O) K (Q) he hA; have hs : Tempo A:=(temperQ S h G K hy).sub (savior P S.land); refine ⟨centsT (x:=0) ?_ hs,hA,hH,?_,hs⟩
    · have hU:sunny P S.land c = 1-Q*(O)⁻¹*(Q)ᴴ:= (Pine.bare_this ..).trans (heir ..).symm
      have hx:H' * K * V₀= H'*W*V₀+H'*μ*V₀:=by rw [hK,Matrix.mul_add,Matrix.add_mul]
      rw [hU]; unfold Z D; rw [hX]; change Cent id id m _ ((1- Q*(O)⁻¹*(Q)ᴴ + (H'*K*V₀- H'*K*D*K*V₀))-(1-Q*(O)⁻¹*(Q)ᴴ)); rw [hx,add_sub_cancel_left];
      have h1: Ton (R).embed (R).embed m (w^2*b) (H'*W*V₀):= Ton.up (((hl.op hB hz hb).op hr (mul_nonneg hz hb) hz)) (le_of_eq (by ring))
      have h2: Ton (R).embed (R).embed m (2*w^3*a^2) (H'*K*D*K*V₀):=by apply Ton.up (((((hl.op hc hz ha).op hH (by positivity) (by positivity)).op hc (by positivity) ha).op hr (by positivity) hz)); exact le_of_eq (by ring)
      have hξ:= Cent.smul hp (-1); rw [norm_neg,norm_one,one_mul,neg_one_smul] at hξ; have hf:= Cent.sub (maple R _ h1).toR hξ; rw [sub_neg_eq_add] at hf; exact Cent.sub hf (maple R _ h2).toR
    have hh' : D*(Q)ᴴ-V₀= -(D*K*V₀):=by change _ -(O)⁻¹*(Q)ᴴ= _; unfold D; rw [h']; unfold V₀ proton conn; rw [Matrix.mul_assoc _ (O)⁻¹]; abel
    change Ton _ _ _ _ (D * (Q)ᴴ- V₀); rw [hh']; exact Ton.up (((hH.op hc (by positivity) ha).op hr (by positivity) hz).neg) (le_of_eq (by ring))
end YM.QCD.Globe
