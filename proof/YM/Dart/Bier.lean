import YM.Dart.Wound
/-!
  A discrete telescoping measurement of one-slot derivative budget. Does not
  pay powers of lattice size and doesn't extrapolate through interpolation.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Needle
open Set Function Filter Lattice Cells Lyre Lyre.Goblet Romance QCD QCD.Lat QCD.Tide QCD.Grass Plum QCD.RP Patria Patria.Depth Patria.Hub Intag Intag.Vale
open Finset UV Poised Poised.Plans Poised.Plans.Stamp Poised.Stative
open scoped Topology ContDiff BigOperators Classical ComplexOrder
variable {C:Sequence} (P:Calibration C) (d:ℕ)
local notation "S"=> C.S
set_option quotPrecheck false
local notation "a" i:arg=> C.S.spacing (C.N i)
noncomputable def shifting (C:Sequence) (i:ℕ)(v:Cover)(U:stalk C i):stalk C i:=fun x=>U (x+v)
noncomputable def lDer (C:Sequence)(i:ℕ)(b:Axis): stalk C i→ₗ[ℂ]stalk C i where
    toFun x:= ((↑(C.S.spacing (C.N i)):ℂ)⁻¹) • (shifting C i (step b) x-x)
    map_add' x y:=by ext1 i; simp only [shifting,Pi.smul_apply,Pi.sub_apply,Pi.add_apply]; rw [add_sub_add_comm, smul_add]; -- ok
    map_smul' t x:=by ext1 p; simp only [shifting,Pi.smul_apply,Pi.sub_apply,RingHom.id_apply]; rw[←smul_sub, smul_comm]
variable {P d} {E:Hub.Invest P d}(H:Rack E)
namespace GaugeP
variable {Z: Laurel d}{J: Landing P.sym Z}(K:GaugeP P Z J){β ν:ℝ}(hp:C.Path β ν)(hS:Sway C.S)(G:Capital P d 1)
variable {H}(x:(i:ℕ)→stalk C i){P₀:ℕ→ Label d}
-- choose genuine fine support interior.
variable (b:Axis)
noncomputable abbrev poleW (p:Cover):ℕ→ Cover:=fun j=> p + j • step b
lemma pole_dist (p:Cover)(j i:ℕ):dist (digit (C.S.spacing (C.N i)) (poleW b p j)) (digit (C.S.spacing (C.N i)) p)= j*C.S.spacing (C.N i):=by
    have h : digit (a i) (j • (step b:Cover))= ((a i)*j) • basis b:=by
         unfold digit; ext x; simp [basis_eq,step,vector]; split_ifs with he <;> simp_all
    rw [dist_eq_norm,poleW,digit_plus,h,add_sub_cancel_left,norm_smul,basis_norm, mul_one,Real.norm_of_nonneg (mul_nonneg (space0 _ _).le (by positivity)),mul_comm]
include hp
lemma linger : ∃ e:ℝ,0 < e ∧ ∀ᶠ i:ℕ in atTop,∃ p:Cover,∃ n:ℕ,0<n ∧ e ≤ n*a i∧∀ m:ℕ,m≤n→ K.fault i (poleW b p m):=by
    let r:=K.extent; have hr:0<r:=K.breadth; have hS:= tendsto_nhds_of_tendsto_nhdsWithin hp.physical; refine ⟨r/8,(by positivity),?_⟩
    filter_upwards [hS.eventually_le_const (show 0<r/8 from by positivity)] with i hi
    let M:= ⌈(r/8)/(a i)⌉₊; have hx :0<a i:=space0 _ _; let p:=bead (a i) K.coast
    have hM:0<M:=Nat.ceil_pos.mpr (by positivity)
    have hk:(M:ℝ)*a i ≤ r/8 + a i:=by
         apply (mul_le_mul_of_nonneg_right (le_of_lt (Nat.ceil_lt_add_one (show 0≤r/8 / a i by positivity))) hx.le).trans; rw [add_mul,one_mul, div_mul_cancel₀ _ hx.ne']
    refine ⟨p,M,hM,(div_le_iff₀ hx).1 (Nat.le_ceil _),fun m h=>?_⟩
    refine Metric.mem_closedBall.mpr ((dist_triangle _ (digit (a i) p) K.coast).trans ?_)
    rw [pole_dist]; have hu :=smoothV hx K.coast; have ht:M*a i ≤ r/8+a i:=hk
    have hb: (m:ℝ)*a i ≤ r/8+a i:= le_trans (mul_le_mul_of_nonneg_right (by exact_mod_cast h) hx.le) hk; linarith only [hr, hb, hi, (show dist (digit (a i) p) K.coast ≤2*a i from hu),show K.extent=r from rfl]
omit hp
lemma thread (i:ℕ)(x:stalk C i)(p: Cover): K.heightH i p (lDer C i b x)= ((↑(a i):ℂ)⁻¹) • (K.heightH i (p+step b) x-K.heightH i p x):=by
    unfold lDer; change K.heightH i p (((↑(a i):ℂ)⁻¹) • (shifting C i (step b) x-x)) =_; rw [map_smul,map_sub]; rfl
set_option maxHeartbeats 400000 in
lemma rawS (p:Cover)(i n:ℕ)(hn:0<n)(hx:∀ j:Fin n, K.fault i (poleW b p j.val)) (U:stalk C i): ∃ O:Merit K i,O.testR (lDer C i b U)= (↑((n:ℝ)* (a i)):ℂ)⁻¹ • (K.heightH i (poleW b p n) U- K.heightH i p U):=by
    let u:ℝ:=(n:ℝ)⁻¹; have h0:0<(n:ℝ):=by exact_mod_cast hn
    have hs: (∑ _ : Fin n, u)=1:=by simp[u, hn.ne']
    let x(j:ℕ):=K.heightH i (poleW b p j) U; let O:Merit K i:=⟨n,fun j=>poleW b p j.val, fun _=>u,hx, (fun _=> inv_nonneg.mpr h0.le), hs⟩
    have h: (∑ j:Fin n, (x (j.val+1)-x j.val)) = x n-x 0:=by rw [Fin.sum_univ_eq_sum_range (fun j=>x (j+1)-x j)]; exact Finset.sum_range_sub ..
    let c:ℂ:= ↑u * (↑(a i):ℂ)⁻¹; refine ⟨O,?_⟩
    unfold Merit.testR; rw [LinearMap.sum_apply]; have ht (j:Fin n) : ((↑u:ℂ) • K.heightH i (poleW b p j.val)) (lDer C i b U)= c • (x (j.val+1)-x j.val):=by rw [LinearMap.smul_apply,thread,smul_smul]; congr 1; simp only [x,poleW,add_smul,one_smul,add_assoc]
    change (∑ j:Fin n, ((↑u:ℂ) • K.heightH i (poleW b p j.val)) (lDer C i b U))= _; simp_rw [ht,← Finset.smul_sum,h]; rw [show c= _ from (show c=(↑((n:ℝ)*(a i)):ℂ)⁻¹ from by simp [u,c,mul_comm]),show x 0=K.heightH i p U from (by unfold x; simp [poleW])]
variable (x:(i:ℕ)→stalk C i)
-- General ephemeral envelope.Not strong.
include hp hS G
lemma buyDer (h :∀ᶠ j in atTop,∃ V:ℝ, 0 ≤ V∧∀ᶠ i in atTop, GreenP C i j (x i) V):∃ V:ℝ,0≤V ∧ ∀ᶠ i:ℕ in atTop,∃ O:Merit K i, ‖O.testR (lDer C i b (x i))‖≤V:=by
     obtain ⟨e,he,H⟩:= linger K hp b; obtain ⟨j,⟨Q,hQ,hV⟩,L,hL,hP⟩:= (h.and (K.valves hp hS G)).exists -- order
     let Gθ :ℝ:= L*Q; have hx: 0 ≤Gθ:= mul_nonneg hL hQ; refine ⟨e⁻¹*(Gθ+Gθ),by positivity,?_⟩; filter_upwards [H,hP,hV] with i H hp hv; obtain ⟨p,n,hn,h1,hm⟩:=H
     obtain ⟨O,hO⟩:= rawS K b p i n hn (fun j=> hm _ j.isLt.le) (x i); refine ⟨O,?_⟩; let U:= x i; rw[hO,norm_smul,norm_inv,Complex.norm_real,Real.norm_of_nonneg (he.trans_le h1).le]; refine mul_le_mul (inv_le_inv₀ (he.trans_le h1) he |>.mpr h1) ((norm_sub_le ..).trans (add_le_add (hp _ (hm n le_rfl) U Q hQ hv) (hp _ ?_ _ Q hQ hv))) (norm_nonneg _) (inv_nonneg.mpr he.le)
     simpa [poleW] using hm 0 (Nat.zero_le _)
end GaugeP
end YM.Massive.Needle
#print axioms YM.Massive.Needle.GaugeP.buyDer
