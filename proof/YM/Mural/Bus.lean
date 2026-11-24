import YM.Mural.Truck
/-!
# Convoy module.
 Charges measured absolutely by all exposed families, price can vary over nodes.
 Proximity of support retained with explicit widows. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Comet
open QCD QCD.Grass QCD.Finch QCD.Lat Lattice Wilson RG Function Finset MeasureTheory Filter Fork Laurent Flume Kit Pine
open scoped ContDiff BigOperators Matrix Matrix.Norms.L2Operator Classical Kronecker
open MassiveQCD MassiveQCD.Apron.Grove Plette Lat PaletteT Ribbon Push.AbsoluteSums
variable {c f:Side}{j k N:ℕ}
open QCD.Mural MassiveQCD.Stitch MassiveQCD.Apron.Grove.PrintR Plate Cupola Twist Kites Creek Cove
open Massive Massive.PCAC
-- generic range.S output. 
section prices
variable {V:Type} [AddCommMonoid V] [Module ℂ V] {B B':Set V}{C r s:ℝ}
structure Worth (B:Set V)(x:V)(t:ℝ): Prop where
  tint :∃ (P:Type)(_ :Fintype P)(f:P→V)(v:P→ℂ),(∀ i,f i∈B)∧ ∑ i,‖v i‖ ≤ t∧ x= ∑ i,v i • f i
-- labels payload components need common κ
namespace Worth
lemma nothing (B:Set V)(hr:0≤r): Worth B 0 r:=⟨PEmpty, inferInstance, fun _=>0,fun _=>0,fun i=>i.elim,by simpa,by simp⟩ -- nested.constructor binder
lemma oneP (x:V)(h:x∈ B): Worth B x 1:=by refine ⟨Unit, inferInstance,fun _=>x, fun _=>1,fun _=>h,?_,?_⟩<;>simp
variable {x y:V}
lemma fuel (h:Worth B x r)(hp:r ≤ s):Worth B x s:=by obtain ⟨P,p,f,v,h,ht,hw⟩:=h.tint; exact ⟨_,p,f,v,h,ht.trans hp,hw⟩
lemma rotate (k:ℂ)(h:Worth B x r): Worth B (k • x) (‖k‖*r):=by
    obtain ⟨P,p,f,v,h,hq,hx⟩:=h.tint; refine ⟨P,p,f,fun i=>k*v i,h,?_ , ?_⟩; · simp_rw [norm_mul]; rw [← mul_sum]; exact mul_le_mul_of_nonneg_left hq (norm_nonneg _)
    rw [hx]; simp_rw [Finset.smul_sum,mul_smul]
lemma added (h:Worth B x r)(hp:Worth B y s): Worth B (x+y) (r+s):=by
   obtain ⟨P,p,f,a,hf,h₁,h₃⟩:=h.tint; obtain ⟨Q,q,g,b,hg,h₂,h₄⟩:=hp.tint; refine ⟨P⊕Q, inferInstance, Sum.elim f g, Sum.elim a b,?_ ,?_,?_⟩; · rintro (i|i); exact hf i; exact hg i
   · rw [Fintype.sum_sum_type]; exact add_le_add h₁ h₂
   rw [Fintype.sum_sum_type,h₃,h₄]; rfl
lemma sea {A:Type}(S:Finset A)(f:A→V)(p:A→ℝ)(h:∀ i∈S,Worth B (f i) (p i)): Worth B (∑ i∈S,f i) (∑ i∈S,p i):=by
   induction S using Finset.induction_on with
   | empty=> simp only [Finset.sum_empty]; exact nothing B le_rfl
   | insert i S hi ih=> rw [sum_insert hi,sum_insert hi]; exact added (h _ (mem_insert_self ..)) (ih fun i hi=> h i (mem_insert_of_mem hi))
lemma move {W:Type} [AddCommMonoid W][Module ℂ W] (T:V→ₗ[ℂ] W) {A:Set W}(h:Worth B x r) (ht:∀ x∈B, Worth A (T x) C)(hv:0≤ C): Worth A (T x) (r*C):=by
    obtain ⟨P,p,f,v,h,hV,hx⟩:=h.tint; rw [hx,map_sum]; apply Worth.fuel (sea univ _ (fun i=>‖v i‖ * C) ?_) ?_; · intro i _; rw [map_smul]; exact rotate (v i) (ht _ (h i))
    rw [← sum_mul]; exact mul_le_mul_of_nonneg_right hV hv
end Worth
end prices
-- Speck masks.P.B.Source.Q. Counts even.Log.N.Field frame.D.Title mass.Ph. 
noncomputable abbrev performance (H:Insertion f N)(x y:Site f) := fun i:Rank=> scaleLoad H (apogee x y) i (goodwill ..)
-- skew q pair shapes.
variable {I E:Type}(D:DeckV c N)(D':DeckV f N)(L: YM.Next.Free.Flight j k)(d:f.val=c.val*L.L.val)(K:KernelChoices)(r β:ℝ)(hk:L.patch.Branches K su)
local notation "Fb"=> Rank→ Insertion f N
local notation "Cb"=> Rank→ Insertion c N
variable (X: Insertion f N)(Y:Insertion c N) (x y:Site c) (p q:Site f) 
local notation "sP"=> performance X p q
local notation "sR"=> performance Y x y
local notation "λp"=> (L.visit K d)
local notation "T"=> Transfer.blockMap L K d β r hk
local notation "TX"=> texel L d 0 x p
local notation "TY"=> texel L d 0 y q
noncomputable def haul : (Rank→Insertion f N)→ₗ[ℂ] (Rank→ Insertion f N) where
   toFun:= fun H i=>ascend L d x y p q H i
   map_add' X Y:=funext fun i=> ContinuousMap.ext fun U=> by change (∑ j:Rank,doll (TX U) (TY U) i j • (X j U+Y j U))=_; simp_rw [smul_add,sum_add_distrib]; rfl
   map_smul' z X:=funext fun i=>ContinuousMap.ext fun U=>by change (∑ j:Rank,doll (TX U) (TY U) i j • (z • X j U))= z • (∑ j:Rank,doll (TX U) (TY U) i j • X j U); rw [Finset.smul_sum]; exact sum_congr rfl fun j _=> smul_comm ..
noncomputable def billow : (Rank→Insertion f N)→ₗ[ℂ](Rank →Insertion c N):= ((LinearMap.pi (fun i:Rank=> (T).comp (LinearMap.proj (φ:=fun _:Rank=>Insertion f N) i))).comp (haul L d x y p q)) -- N maybe
local notation "W"=>billow (N:=N) L d K r β hk x y p q
lemma rides (i:Rank) : ascend L d x y p q (performance X p q) i= scaleLoad X (loaded p q L d x y) i (loaded_c ..):=by
    ext1 U; change (∑ j:Rank,doll (TX U) (TY U) i j • (cubeQ (apogee p q) j U • X U))=loaded p q L d x y U i.1 i.2 • X U; simp_rw [cubeQ,smul_smul, ← Finset.sum_smul]; apply congr_arg (· • X U); unfold doll loaded; rw [Fintype.sum_prod_type]; simp only [Matrix.mul_apply, Finset.sum_mul]; rw [sum_comm]; apply sum_congr rfl; intro i _; apply sum_congr rfl; intro k _; ring
variable (he:Y=(Transfer.blockMap L K d β r hk) X)
include he
lemma tune (z:ℂ)(hz:z≠0): (W) sP = (lightS L d 0 x p*star (lightS L d 0 y q)) • sR + z⁻¹ • fun i:Rank=>rebirth L d K r β hk X x y p q z i:=by
    let k:=lightS L d 0 x p*star (lightS L d 0 y q); let C:= cleared p q L d x y; subst Y; ext1 i; change T (ascend L d x y p q sP i)=k • performance (T X) x y i + z⁻¹ • (z • _); rw [rides,inv_smul_smul₀ hz]; have he':scaleLoad (T X) C i (cleared_c ..)=k • performance (T X) x y i:=ContinuousMap.ext fun U=>by
       change (k*apogee x y U i.1 i.2) • ((T X) U)=k • ((apogee x y U i.1 i.2) • ((T X) U)); rw [mul_smul]
    rw [he']; abel
omit he
-- budget certificate family. Score linear combination only on full.E. may later need neutral torus covariance of full M along Act. 
structure TokenP where
   -- clocks.N
   t :ℝ
   f :ℝ
   e :ℝ
   k :ℝ
   v :ℝ
   w :ℝ
   s :ℝ
noncomputable def aisle (p:TokenP)(D:DeckV c N) (x y:Site c) (H:ℂ) : Set (Rank→ Insertion c N):={F|Boast D F x y (Lattice.halo D.O.B {x}) p.t p.f p.e p.k p.v p.w p.s H}
-- Convex linear book. X approximation.
structure ClaimP (G:Set (Rank→ Insertion c N))(Y:Rank→Insertion c N) (X: Rank→Insertion c N)(u v:ℝ):Prop where
 costP :∃ z:ℂ, ∃ F:Rank→ Insertion c N, ‖z‖ ≤ u ∧ Worth G F v ∧ X=z • Y+F
end YM.QCD.Comet
#print axioms YM.QCD.Comet.Worth.move
#print axioms YM.QCD.Comet.tune
