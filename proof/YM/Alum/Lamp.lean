import YM.Alum.Ibis
import YM.Alum.Cords
import YM.Alum.Lit
import YM.Alum.Hoist
/-! Reading scales & geometry at vintage. Universal euclidean coordinates native stencil lifts presented at physical `resolution` r, independent of regulator beyond i. -/
set_option autoImplicit false
noncomputable section
namespace YM.Intag
open Function Filter MeasureTheory RG Lattice Wilson Cells YM.Next.Rank.Station Finset
open Massive Massive.Lyre Massive.Patria.Hub Massive.Patria.Depth Massive.Romance QCD QCD.Tide Push.GridApprox
open scoped BigOperators Classical Matrix.Norms.L2Operator ContDiff Topology TensorProduct
namespace Ibis
open QCD.Lat QCD.Acre QCD.Acre.Stratum.MarchQ QCD.Acre.Stratum.MarchQ.Suburb QCD.Acre.Stratum.MarchQ.Suburb.Talis QCD.Acre.Stratum.MarchQ.Suburb.Sapphire
open YM.Bank.Jule YM.Bank.Kith YM.Bloom.Jar
open MintV Suburb.Melt Suburb.Melt.Lobby
variable (S:Scheme) (L:Side) {D:ℕ}(Hp:Dial D)(z:ℝ)
-- geometry fixed palette.Economic.Role.Pren.Hoop. Heft.Pr.System thickness.
variable (w Uq m K:ℕ)(e v:ℝ)
noncomputable def unveil (z:ℝ):ℕ:= paceN L Hp.R z
noncomputable def pitchC (z:ℝ):ℕ:=⌈v * measureV L Hp.e z⌉₊
local notation "ω"=>measureV L
local notation "H"=>ω Hp.e
local notation "b"=> ω w
structure Room (z:ℝ) : Prop where
     /-- G=A_size, K'=B_size -/
     marks (N:ℕ)(hv:(N:ℝ) = measureV L Hp.e z / measureV L w z) : 2*N < e*measureV L Hp.e z
     bars (N M:ℕ)(h:(N:ℝ)=H z / measureV L w z)(he:(M:ℝ)= measureV L 4 z * (measureV L Hp.βA z * measureV L Hp.e z)): pitchC L Hp v z + N + (M / Uq+102+N) ≤ M/2 ∧ (K+1)*(2*(N/Uq+110+m+4*unveil L Hp z))<N
#print Room
variable (hw:1<L.val)
include hw
lemma light (hk:100*(K+1) ≤ Uq) (he:Hp.R < Hp.e) (hδ:0<w)(hv:w<Hp.e) (hx:0<e)(ht:0<v) : ∀ᶠ z in atTop, Room L Hp w Uq m K e v z:=by
    let r(z:ℝ):=unveil L Hp z
    let g(x:ℝ):ℝ:= ↑(K+1)*100*(110+m+4*(r x)) -- wrong casts Tmulℝ or → Nat; choose explicit
    let A:=max w Hp.R; have hG:PageP L g A:=by
        have h1:=PageP.budget_lo (A:=Hp.R) L (le_max_right w Hp.R); have ht : g= (fun x:ℝ=> ((↑(K+1):ℝ)*100)*((110:ℝ)+(m:ℝ)+4*measureV L Hp.R x)):= by funext x; unfold g; rw [pitchN]; rfl
        rw [ht]; exact (PageP.just L _ A|>.harm L (h1.timesL L 4)).timesL L _
    have hB:= hG.times L (PageP.budget_lo (A:=w) L (le_max_left w Hp.R));
    have hh1 : ∀ᶠ z:ℝ in atTop, (16:ℝ)*(v+110) ≤ measureV L 4 z := PageP.cheaper _ (PageP.just _ _ 0) hw (by norm_num)
    have hh2 : ∀ᶠ z:ℝ in atTop, (3:ℝ)/e ≤ measureV L w z:=PageP.cheaper _ (PageP.just _ _ 0) hw hδ
    filter_upwards [PageP.cheaper L hB hw (show A < Hp.e from max_lt hv he), hh1,hh2] with z hB h₁ h₂ -- max_lt?
    let P:=measureV L Hp.e z; let B:=measureV L w z; have hp0:1 ≤ P:=uniformV ..; have hP:0<P:=χone ..; have hp:1≤ B:= uniformV ..; have hxB:0<B:=χone ..
    have hQ:0 < Uq:=by omega
    have h₂:3/e ≤ B:=h₂
    constructor -- remove field space
    · intro N h; change (N:ℝ)=P/B at h; change 2*(N:ℝ) < e * P; rw [h]; rw [←mul_div_assoc,div_lt_iff₀ hxB]; have hy:= mul_lt_mul_of_pos_left (lt_of_lt_of_le (show (2:ℝ)<3 from by norm_num) ((div_le_iff₀ hx).mp h₂)) hP; nlinarith only [hy]
    intro N M h hx; let X:=pitchC L Hp v z; let Y:=M / Uq; let Z:= N / Uq; change (N:ℝ)=P/B at h
    have hu:(N:ℝ) ≤ P:=h.le.trans (div_le_self hP.le hp)
    have h': (16:ℝ)*(v+110)*P ≤ M:= by
          have Hx:=mul_le_mul_of_nonneg_right h₁ hP.le; have ht:=uniformV L z Hp.βA -- arity inspect; 
          rw [hx]; apply Hx.trans; exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hP.le ht) (χone ..).le
    have hY: Y*Uq ≤ M:= Nat.div_mul_le_self ..
    have h:2*(K+1)*Z*50 ≤ N:= le_trans (le_of_eq (show 2*(K+1)*Z*50= Z*(100*(K+1)) by ring)) ((Nat.mul_le_mul_left _ hk).trans (Nat.div_mul_le_self _ _)) -- linter h shadows.P
    have hS : 8*Y ≤ M:= by
       have he: 8*Y ≤ Y*Uq:= by rw[mul_comm]; exact Nat.mul_le_mul_left Y (by omega)
       exact he.trans hY
    have htV : (X:ℝ) ≤ v*P+1:= (Nat.ceil_lt_add_one (mul_nonneg ht.le hP.le)).le
    constructor
    · have hg:8*(X+2*N+103) ≤ M:= by
            exact_mod_cast (show (8:ℝ)*((X:ℝ)+2*N+103) ≤ (M:ℝ) from by nlinarith only [htV,hp0,h',hu, ht])
      change X+ N+ (Y+102+N) ≤_; omega
    have h': g z ≤ (N:ℝ):=by
          change _ ≤ _; rw [‹(N:ℝ)=P/B›]; exact (le_div_iff₀ hxB).2 hB
    have hy:(K+1)*100*(110+m+4*unveil L Hp z) ≤ N:=by unfold g at h'; exact_mod_cast h'
    have hz0:0<(K+1)*(110+m+4*unveil L Hp z):=by positivity
    generalize ht : 110+m+4*unveil L Hp z=W at * -- but expression inside ((Z+110)+m+4*) not got
    change (K+1)*(2*(Z+110+m+4*unveil L Hp z))<N
    rw [show Z+110+m+4*unveil L Hp z=Z+W from (by omega)]
    nlinarith only [hy,h,hz0] -- test
end Ibis
end YM.Intag
#print axioms YM.Intag.Ibis.light
