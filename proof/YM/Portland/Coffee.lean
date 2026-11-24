import YM.Portland.Pour
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Comet
open QCD QCD.Grass QCD.Finch QCD.Lat Lattice Wilson RG
open Function Finset MeasureTheory Filter Fork Laurent Flume Kit Pine
open scoped Topology ContDiff BigOperators Matrix Matrix.Norms.L2Operator Classical Kronecker
open MassiveQCD MassiveQCD.Apron.Grove Plette Lat
open PaletteT Ribbon
variable {c f:Side}{j k N:ℕ}
open QCD.Mural MassiveQCD.Stitch MassiveQCD.Apron.Grove.PrintR Plate Cupola Twist Kites Creek Cove
open NormedSpace Grass.Ovule
variable {I E:Type}(Z:PrintR f N Rank I E)(D:DeckV f N)(i:Rank)
set_option quotPrecheck false
local notation "QO"=>D.O
local notation "D1"=>D.E 1
local notation "Kt"=> rootR (Spine Unit) (Keys f N)
local notation "WE"=> pluck (Keys f N) sD
local notation "eq0"=>D.density (1:Grid f)
-- cylinder to estimates at Identity.C.
variable (x y:Site f)(U:TokenP)(α:ℂ)
local notation "ℒ"=> repay (univ:Finset (Keys f N)) U.t 4 (fun _=>U.f)
open Massive
local notation "K'"=> aisle U D x y α
variable (X:Rank→ Insertion f N)
local notation "Rκ"=> (α • D.density 1)
variable (h1:1 ≤ U.t)(h2:1≤ U.f)(h3:0≤U.e)(h4:0≤U.k)(h5:1≤U.w)(h6:0≤U.v)
include h1 h2 h3 h4 h5
lemma under (h:X∈ aisle U D x y α) : ∃ (Y:Alg (Keys f N)), Plus Y ∧ X i 1=(α • eq0)*Y ∧ ℒ Y≤ U.v:=by
    obtain ⟨I,E,hi,he,Z,hP,hZ,hΩ⟩:= (show Boast D X x y (halo D.O.B {x}) U.t U.f U.e U.k U.v U.w U.s α from h).expo -- type annotate
    let t:= halo D.O.B {x}; let P:= (Z.regE (some i)).rope D.O.threshold 1
    refine ⟨WE P,brightness Z D i,?_,?_⟩; · rw [hΩ,ink Z D i x y t hP]; exact smul_mul_assoc ..|>.symm
    exact hpBoast Z D i x y t U hP hZ (Lattice.halo_spec.mpr ⟨x,mem_singleton_self _,by simp⟩) h1 h2 h3 h4 h5
variable {r s:ℝ}
include h6
lemma earnedB (h: Worth (aisle U D x y α) X r):∃ Y:EvenA f N,X i 1=Rκ*Y.val∧ℒ Y.val≤r*U.v:=by
    obtain ⟨P,hp,Z,v,hZ,hq,hW⟩:=h.tint; choose V hv hm H using fun p=>under D i x y U α (Z p) h1 h2 h3 h4 h5 (hZ p)
    let F0(j): EvenA f N:= ⟨V j,hv j⟩; let g:EvenA f N:=∑ j:P,v j • F0 j; have hΓ:g.val=∑ j:P,v j • V j:=by change light _ (∑ j:P,v j • F0 j)=_; simp only [map_sum,map_smul]; rfl
    refine ⟨g,?_,?_⟩; · rw [hW,hΓ,mul_sum,Finset.sum_apply,ContinuousMap.sum_apply]; refine sum_congr rfl fun j _=>?_ ; change v j • ((Z j) i 1)=_; rw [hm,mul_smul_comm]
    rw[hΓ]; refine (repay_sum ..).trans (le_trans (b:=∑ j:P,‖v j‖*U.v) (sum_le_sum fun j _=>?_) ?_)
    · rw [repayL]; exact mul_le_mul_of_nonneg_left (H j) (norm_nonneg _)
    rw [← sum_mul]; exact mul_le_mul_of_nonneg_right hq h6
variable (Y: Insertion f N)(hY:Y 1=α • D.density 1)
local notation "bι"=> (U.t*U.f)
lemma pricePromoted {A:Type*}[Fintype A](x: Alg A)(n:ℕ)(hn:n ≤4): bins A x n≤(n.factorial:ℝ)*(repay (univ:Finset A) U.t 4 (fun _=>U.f) x / (U.t*U.f)^n):=by
      refine (prices x n).trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)); rw [le_div_iff₀ (pow_pos (mul_pos (zero_lt_one.trans_le h1) (zero_lt_one.trans_le h2)) _),Mural.sheet _ _ _ _ h1 (fun _=>zero_lt_one.trans_le h2)]; unfold priceD; rw [sum_mul]; let F i:= premium (univ:Finset A) U.t 4 i*‖coef i x‖*load (fun _=>U.f) (mono i)
      let S:= univ.filter (fun i:Finset A=>i.card=n); refine le_trans (b:=∑ i∈S,F i) (sum_le_sum fun i hi=>?_) (sum_le_sum_of_subset_of_nonneg (subset_univ _) fun i _ _=>by have hk:0 ≤ F i:= mul_nonneg (mul_nonneg (premNN _ _ _ h1) (norm_nonneg _)) (load_nn ..); exact hk)
      have hp:= (mem_filter.mp hi).2; unfold F; rw [ticket_mono (fun _=> U.f) i (fun _=>zero_lt_one.trans_le h2),prod_const,premium,inter_univ,hp,min_eq_right hn, mul_pow]; exact le_of_eq (by ring)
include hY
structure BreezeX (x:Alg (Keys f N))(t a b:ℝ) (X:Insertion f N):Prop where
    owns:∃ y:Alg (Keys f N),Plus y ∧ X 1=x*y ∧ bins (Keys f N) y 0≤t ∧ bins (Keys f N) y 2≤a ∧ bins (Keys f N) y 4 ≤ b
noncomputable def bronze (U:TokenP)(s:ℝ)(n:ℕ):= (n.factorial:ℝ)*(s*U.v/(U.t*U.f)^n)
lemma emergeB (h:ClaimP (aisle U D x y α) (performance Y x y) X r s): BreezeX Rκ (r+s*U.v) (bronze U s 2) (bronze U s 4) (X i):=by
      obtain ⟨z,F',hv,hK,hr⟩:= h.costP; obtain ⟨E',hx,h⟩:= earnedB D i x y U α F' h1 h2 h3 h4 h5 h6 hK
      let φ:=apogee x y 1 i.1 i.2; have he: ‖φ‖≤1:=by unfold φ; rw [remainsX]; by_cases h:i.1=i.2<;>simp [Matrix.one_apply,h]
      let G:= z • (φ • (1:Alg (Keys f N))); let M:= G+E'.val; refine ⟨M,show grade _=_ from ?_,?_, ?_⟩
      · unfold M G; rw [map_add,map_smul,map_smul,map_one,show grade E'.val=E'.val from bright E']
      · unfold M; rw [hr,mul_add]; change z • (φ • Y 1) + F' i 1=_; rw [hx,hY,mul_smul_comm,mul_smul_comm,mul_one]
      have hG : ‖Grass.Ovule.core _ G‖≤r:=by unfold G; rw [map_smul,map_smul,map_one,norm_smul,norm_smul,norm_one,mul_one]; exact (mul_le_of_le_one_right (norm_nonneg _) he).trans hv
      let N0 n:= bronze U s n
      have hN(n:ℕ)(hn:n≤ 4): bins (Keys f N) E'.val n≤bronze U s n:=(pricePromoted U h1 h2 h3 h4 h5 h6 E'.val n hn).trans (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right h (pow_nonneg (mul_nonneg (zero_le_one.trans h1) (zero_le_one.trans h2)) _)) (Nat.cast_nonneg _)) -- order likely implicit
      have hr' (n:ℕ)(hz:n≠0): bins (Keys f N) G n=0:=by rw [show G=z • (φ • (mono ∅)) by rw[mono_empty],r_const,r_const,Grass.Ovule.wings,card_empty,if_neg (Ne.symm hz),mul_zero,mul_zero]
      exact ⟨ (r_tri G _ 0).trans (add_le_add hG (by simpa [bronze] using hN 0 (by omega) : bins (Keys f N) E'.val 0≤ s*U.v)), (r_tri G _ 2).trans (by rw[hr' _ (by decide), zero_add]; exact hN _ (by omega)),(r_tri G _ 4).trans (by rw[hr' _ (by decide),zero_add]; exact hN _ (by omega))⟩
lemma birthW (n:ℕ)(M:PCAC.Deck f N)(a b:Dye N)(h: Invoice D M n U Y α r s)(ht:separation x y≤n): BreezeX (α • eq0) (r+s*U.v) (bronze U s 2) (bronze U s 4) (M (idx x a i.1) (idx y b i.2)):=
      emergeB D i x y U α _ h1 h2 h3 h4 h5 h6 Y hY (h.income x y ht a b)
end YM.QCD.Comet
#print axioms YM.QCD.Comet.birthW
