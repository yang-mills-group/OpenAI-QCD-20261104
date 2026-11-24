import YM.Arise.Pair
import YM.Massive.Target.Calibration
/-! # Exterior Wick observations actual.W support comparison.T express.Any finite-alphabet factors.C -/
set_option autoImplicit false
noncomputable section
namespace YM.Arise.Count
open Function Lattice Finset Wilson Filter MeasureTheory Tensor Work.G06 RG
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical Pointwise TensorProduct
open Analysis Massive UV UV.Free QCD QCD.Grass
variable {r n m i j k d D:ℕ}
variable {G: Gauge}
variable {A I E:Type*}
variable {s t u :ℝ}
-- Multilinear induction.Expose.S.Engine
section
open MultilinearMap
variable {B :Type*}{o:Fin n→Type*}{M:Fin n→ Type*}[∀ i,AddCommMonoid (M i)][∀ i,Module ℂ (M i)][AddCommMonoid B][Module ℂ B]
lemma roof (f g: MultilinearMap ℂ M B)(p:∀ i,Module.Basis (o i) ℂ (M i))(h:∀ (u:∀ i,o i),f (fun i=>p i (u i))=g (fun i=>p i (u i))): f=g:=by ext1 x; rw [Multilabel.expansion p f, Multilabel.expansion p g]; apply Finset.sum_congr rfl; intro i _; rw [h] -- rw f p
-- interpolation any fixed bi-action on Tensor factor multilinear
end
section Cone
open TensorProduct
variable {U V:Type}
-- dictionary Spin
abbrev Arms (d:I→ℕ):= (i:I)× Pairs (SpinMode (d i))
noncomputable def callS (x:I→E4)(d:I→ℕ): Matrix (Arms d) (Arms d) ℂ:= Matrix.of fun i j=> if x i.1=x j.1 then 0 else Sum.elim (fun v=>Sum.elim (fun _=>0) (fun s=>leg v s (x i.1) (x j.1)) j.2) (fun _=>0) i.2
lemma nextX (x: Points n)(hx:x∈conf n)(d:Fin n→ℕ) (p q: Occ d): UV.Free.pair x p q=callS (fun i=> x i) d p q-callS (fun i=>x i) d q p:=by
    unfold UV.Free.pair callS; simp only [Matrix.of_apply]; by_cases h:p.1=q.1; · simp [h]
    rw [if_neg h, if_neg ((show Injective x.ofLp from hx).ne h),if_neg ((show Injective x.ofLp from hx).ne (Ne.symm h))]; rcases p with ⟨i,v|w⟩<;> rcases q with ⟨j,k|l⟩<;> simp
-- M multilinearity split tensor.Products. ensure embedding true
open Pair
variable (J:Type) [Fintype U][Fintype J]
noncomputable def erg (x:J→E4)(d:J→ℕ): Alg (Arms d)→ₗ[ℂ]Alg U:= (offP _ _).toLinearMap.comp ((QCD.Creek.birth (QCD.Anomaly.Wand (callS x d))).toLinearMap)
noncomputable def ham (i : J)(d:J→ℕ): SpinPol (d i) →ₐ[ℂ] Alg (Arms d):= embed (fun v=> ⟨i,v⟩)
variable (f:Fin n→J) (d₂:J→ℕ)(x:J→ E4)
lemma worlds (v:(i:Fin n)→SpinPol (d₂ (f i))) : ∃ L: MultilinearMap ℂ (fun i:Fin n=>SpinPol (d₂ (f i))) (Alg (Arms d₂)),∀ v, L v=(List.ofFn (fun i=> ham J (f i) d₂ (v i))).prod:=⟨(MultilinearMap.mkPiAlgebraFin ℂ n (Alg (Arms d₂))).compLinearMap (fun i=> (ham J (f i) d₂).toLinearMap), fun i=> MultilinearMap.mkPiAlgebraFin_apply (R:=ℂ) (fun j=> ham J _ d₂ (i j))⟩ -- arg order?
lemma spin_h (hx:points (x ∘ f)∈conf n)(p:(i:Fin n)→ Finset (Pairs (SpinMode (d₂ (f i))))) : let l:List (Occ (d₂ ∘ f)) := (List.finRange n).flatMap fun i => (atomList (p i)).map (fun a=> (⟨i,a⟩:Occ (d₂∘ f))); erg J (U:=U) x d₂ (List.ofFn (fun i:Fin n=>ham J (f i) d₂ (mono (p i)))).prod= pf (UV.Free.pair (points (x∘ f))) l.length l • (1:Alg U) :=by
       intro l; let y:=points (x∘ f); let g(i:Occ (d₂∘ f)):Arms d₂:= ⟨f i.1,i.2⟩; let Z:=callS x d₂; let K(i j: Arms d₂):= Z i j-Z j i
       have hQ (i:Fin n) : ((atomList (p i)).map (fun a=> atom (g (⟨i,a⟩:Occ (d₂∘f))))).prod=ham J (f i) d₂ (mono (p i)):=by  let L:=ham J (f i) d₂; let r(a:Pairs (SpinMode (d₂ (f i)))):=atom (g ⟨i,a⟩); let b:=(expression (p i)).choose; change _=L (mono _); rw [show mono (p i)=_ from (expression (p i)).choose_spec.2.2,map_list_prod]; congr 1; change ((List.ofFn b).map r)=_; rw [List.map_ofFn,List.map_ofFn]; congr 1; funext a; change atom (A:=Arms d₂) _= L _; exact (embed_atom (fun v=> (⟨f i,v⟩:Arms d₂)) _).symm -- nonsensical T let
       have he: (List.ofFn (fun i:Fin n=>ham J (f i) d₂ (mono (p i)))).prod=((l.map g).map atom).prod:=by
           unfold l; simp only [List.map_flatMap, List.map_map]; let L:= (List.finRange n); let h(i:Fin n):=(atomList (p i)).map (fun a=> atom (g (⟨i,a⟩:Occ (d₂∘f))))
           have he(L:List (Fin n)) : (L.flatMap h).prod=(L.map (fun i=> (h i).prod)).prod:=by induction L with|nil=>rfl|cons a b ih=>simp [ih]
           change _= (L.flatMap h).prod; rw [he]; unfold L; congr 1; unfold h; simp_rw [hQ]; rw [List.finRange,List.map_ofFn]; rfl
       rw [he]; refine (seal0 (U:=U) Z l.length (l.map g) (List.length_map g|>.le)).trans ?_; change pf K _ _ • _ = _; rw [clefts g (@UV.Free.pair _ (d₂∘f) y) K (?_)]; intro i j; exact nextX y hx _ i j
-- Wick splitting on arbitrary symbol and tensor factors
lemma gammaCost (hx:points (x∘f)∈conf n) (P:Fin n→UV.GPol)(V:(i:Fin n) →SpinPol (d₂ (f i))): erg J x d₂ (List.ofFn (fun i:Fin n=> ham J (f i) d₂ (V i))).prod |> fun z=> Maxwell.Wick.moment su (points (x∘f)) (fun i=>Maxwell.reduceEq (P i)) • z= UV.Free.moment (d₂∘ f) (points (x∘f)) (fun i=> P i⊗ₜ[ℂ] V i) • (1:Alg U):=by
     let x':= points (x∘f); let G₀:= Maxwell.Wick.moment su x'; let M:=UV.Free.moment (d₂ ∘ f) x'
     let p' i:=MvPolynomial.basisMonomials (Labels.Key su) ℂ i; let Q(i:Fin n):=blades (Pairs (SpinMode (d₂ (f i)))); let X(i:Fin n) := SpinPol (d₂ (f i))
     obtain ⟨L,hL⟩:=worlds J f d₂ V
     let Y:= LinearMap.toSpanSingleton ℂ (Alg U) (1:Alg U); let T: MultilinearMap ℂ (fun _:Fin n=> UV.GPol) ℂ:= G₀.compLinearMap fun i=> Maxwell.reduceEq.toLinearMap; let U': MultilinearMap ℂ X (Alg U):=(erg J x d₂).compMultilinearMap L
     have ht(s:(i:Fin n)→Finset (Pairs (SpinMode (d₂ (f i))))) (v:(i:Fin n)→ SpinPol (d₂ (f i))) (h:∀ i,v i= Grass.mono (s i)) : T P • U' v= M (fun i=>P i⊗ₜ[ℂ] v i) • (1: Alg U) :=by -- metavars wrong? specify
         let V i:=v i; let L':=LinearMap.toSpanSingleton ℂ (Alg U) (U' v); let PA:= M.compLinearMap fun i=>(TensorProduct.mk ℂ UV.GPol (X i)).flip (v i)
         change (L'.compMultilinearMap T) P=(Y.compMultilinearMap PA) P; apply DFunLike.congr_fun (roof _ _ (fun _=>MvPolynomial.basisMonomials _ _) ?_) P
         intro k; let b(i): PowerPair (d₂ (f i)):= (k i,s i); have hf: U' v=erg J x d₂ (List.ofFn (fun i=> ham J (f i) d₂ (mono (s i)))).prod:= by unfold U'; rw [LinearMap.compMultilinearMap_apply,hL]; simp_rw [h]
         let g i:= p' (k i); have hu:PA g=M (fun i=> basisU _ (b i)):=congr_arg M (funext fun i=>by change g i ⊗ₜ[ℂ] v i= (basisU (d₂ (f i)) (k i,s i)); rw [h,basisU,Module.Basis.tensorProduct_apply]; rfl)
         change L' (T g)=Y (PA g); change T g • U' v=PA g • (1:Alg U); rw [hu,hf,spin_h J f d₂ x hx]; unfold M; rw [ UV.Free.moment,Multilabel.applyBasis]; exact smul_smul ..
     change T P • erg J _ _ _= _; rw [← hL V]; change T P • U' V=M (fun i=> P i ⊗ₜ[ℂ] V i) • _
     let fA:= M.compLinearMap fun i=>TensorProduct.mk ℂ _ _ (P i)
     change ((T P) • U') V=(Y.compMultilinearMap fA) V; apply DFunLike.congr_fun (roof _ _ Q ?_) V; intro v; exact ht v _ (fun _=>rfl)
end Cone
end YM.Arise.Count
#print axioms YM.Arise.Count.gammaCost
