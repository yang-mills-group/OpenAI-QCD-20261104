import YM.QCD.Globe.Meal
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
open Laurent Fork
-- compare all ∀o legs with mandatory.FIX m=6
variable (S h)
def vial (X:Kit.Rail f c)(o:Site f) (v:Cover): Alder c:= occ o v • cell X (o+wrap _ v)
lemma vialK (X:Kit.Rail f c)(o:Site f)(j:Axis): vial (Flume.after X j) o= stepA j (vial X o):=by
    funext p q; have he: occ (o+wrap f p) (step j)=seam 0 (o+wrap f p) j := by
       rw [show (step j:Cover) = stop 0 [posDir j] from (by change step j= 0 +step j; rw [zero_add]), ← Quarry.occ_rays]
       unfold Revolve.shimmer Revolve.glint; simp [Step.used, posDir, Revolve.shimmer]
    unfold stepA vial; rw [Pi.smul_apply,Pi.sub_apply,Pi.smul_apply,Pi.smul_apply,sign_rate, map_add, ← add_assoc, wrap_step]; rw [he,Brick.karma,smul_sub,smul_smul]
def tithe (X:Kit.Rail f c)(r:Ratio c f)(A:ℝ)(m:ℕ):Prop:=∀ l: List Axis,l.length ≤2→Cent r.parent id m (A*((r.count.val:ℝ)⁻¹)^l.length) (oldDiff X l)
def remnant (v:Cover)(X:Cover→ Alder c):= X v-X 0-firstA v X
variable {X:Kit.Rail f c}{r:Ratio c f}{A:ℝ}{M:ℕ}
lemma mast (he:tithe X r A m)(v:Cover)(hk:size v≤ M)(u:List Axis)(hu:u.length≤2)(o:Site f): fir (r.parent o) m (vial (oldDiff X u) o v)≤ A*((2+(M:ℝ)*(r.count.val:ℝ)⁻¹)^m*((r.count.val:ℝ)⁻¹)^u.length):=by
    unfold vial; rw [fir_s,pathLength,one_mul]; exact (percept r v (oldDiff X u) o hk (he u hu)).trans_eq (by ring)
-- near <= L gets second differences bound, far (> L) use old + affine
variable {u:ℝ}
private lemma summate (v w:ℝ)(n:ℕ)(he:2≤n)(ht:0≤v)(hm:0≤w)(hv:v≤1)(h:1≤v*w): (2+w*v)^n+3^n+ w*(3^n*v) ≤ 3*3^n*(1+w)^n*v^2:=by
    let b:=v*w; have hp: 0<b:=zero_lt_one.trans_le h
    have hQ:(2+w*v)^n ≤3^n*b^n:=by rw [← mul_pow]; apply pow_le_pow_left₀ (by positivity); unfold b; linarith
    have hm: b^n ≤(1+w)^n*v^2:=by unfold b; rw [mul_pow, mul_comm]; exact mul_le_mul (pow_le_pow_left₀ hm (le_add_of_nonneg_left zero_le_one) n) (pow_le_pow_of_le_one ht hv he) (pow_nonneg ht n) (show (0:ℝ)≤(1+w)^n by positivity)
    have hu: 1≤ b^n:=one_le_pow₀ h
    have hx: b ≤ b^n:=le_self_pow₀ h (by omega)
    -- rewrite last item
    rw [show w*((3:ℝ)^n*v)= (3:ℝ)^n*b by unfold b; ring]; linarith only [hQ,mul_le_mul_of_nonneg_left hm (pow_nonneg (show (0:ℝ)≤ 3 by norm_num) n),mul_le_mul_of_nonneg_left hu (pow_nonneg (show (0:ℝ) ≤ 3 from by norm_num) n),mul_le_mul_of_nonneg_left hx (pow_nonneg (show (0:ℝ) ≤ 3 from by norm_num) n)]
lemma reminisce (o: Site f)(v:Cover)(hz:size v ≤ M)(h: tithe X r A m)(hp:2≤ m)(hA:0 ≤ A) : fir (r.parent o) m (remnant v (vial X o)) ≤ A*(3*3^m*((r.count.val:ℝ)⁻¹)^2)*(1+(M:ℝ))^m:=by
    let L:ℝ:=r.count.val; let i:=L⁻¹; have hL: 1 ≤ L:=by unfold L; exact_mod_cast r.count.property
    have hi: 0< i:=inv_pos.mpr (zero_lt_one.trans_le hL)
    have hi':i≤1:=inv_le_one_of_one_le₀ hL
    let q u:= oldDiff X u; have hF (u:List Axis)(he:u.length≤2)(x:Cover)(h:size x ≤ M):fir (r.parent o) m (vial (q u) o x) ≤ A*((2+M*i)^m*i^u.length):= mast (by assumption) x h u he o -- name h shadows
    cases le_total (M*i) 1 with
    | inl ht=>
      have hh : fir (r.parent o) m (remnant v (vial X o))≤ M^2*(A*(3^m*i^2)):=by
        unfold remnant; refine firstH _ v M hz _ ?_ (by positivity); intro a b x he
        have hx : vial (q [b,a]) o=stepA b (stepA a (vial X o)):=by unfold q oldDiff; rw [vialK,show oldDiff X [a]=Flume.after X a from rfl,vialK]
        rw [← hx]; apply le_trans (hF [b,a] (by simp) x he); simp only [List.length_cons, List.length_nil]; gcongr; linarith
      have he : (M:ℝ)^2 ≤ (1+M:ℝ)^m:=le_trans (pow_le_pow_left₀ (Nat.cast_nonneg _) (le_add_of_nonneg_left (show (0:ℝ)≤1 by norm_num)) 2) (pow_le_pow_right₀ (by simp) hp)
      refine hh.trans ?_; change _ ≤ A*(3*(3:ℝ)^m*i^2)*(1+(M:ℝ))^m; nlinarith only [mul_le_mul_of_nonneg_right he (show 0≤A*((3:ℝ)^m*i^2) by positivity), mul_nonneg (show (0:ℝ)≤(1+(M:ℝ))^m by positivity) (show 0≤A*((3:ℝ)^m*i^2) by positivity)]
    | inr ht=>
      let W:=vial X o; let B:=fir (r.parent o) m
      have hs (u:List Axis)(hu:u.length ≤ 2): B (vial (q u) o (0:Cover)) ≤ A*(3^m*i^u.length):=by
          have hx := mast h (0:Cover) (M:=0) (by simp [Laurent.size]) u hu o; apply hx.trans; simp only [Nat.cast_zero,zero_mul, add_zero]; change A*((2:ℝ)^m*i^u.length) ≤ _; gcongr; norm_num
      have h1:B (W v) ≤ A*(2+(M:ℝ)*i)^m:=by have he:=hF [] (by simp) v hz; rw [List.length_nil,pow_zero,mul_one] at he; exact he
      have h2:B (W 0)≤ A*3^m:=by have he:=hs [] (by simp); rw [List.length_nil,pow_zero,mul_one] at he; exact he
      have h3 :B (firstA v W) ≤ M*(A*(3^m*i)):=by
         apply le_trans (first_bill _ W (t:=A*(3^m*i)) ?_ v) (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hz) (by positivity)); intro a; have he:= hs [a] (by simp); rw [List.length_cons,List.length_nil, Nat.zero_add,pow_one, show q [a]=Flume.after X a from rfl,vialK] at he; exact he
      apply (fir_h ..).trans ((add_le_add ((fir_h ..).trans (add_le_add h1 h2)) h3).trans ?_); have hs:=mul_le_mul_of_nonneg_left (summate i M m hp hi.le (Nat.cast_nonneg _) hi' (by linarith)) hA; change _ ≤ A*(3*3^m*i^2)*(1+(M:ℝ))^m; linarith only [hs]
end YM.QCD.Globe
