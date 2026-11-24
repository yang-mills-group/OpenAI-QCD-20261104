import YM.QCD.Cove.Drip
import YM.QCD.Step.Gallery
/-! # Joint Alphabet ties shearing law to dollar algebra. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Cove
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {F:ℕ}{t:ℝ}{f c: Side}{S: Ratio c f}

abbrev Junta (c f : Side)(F:ℕ):=Pairs (Modes f F⊕Modes c F)
abbrev Water (c f:Side)(F:ℕ) := Matrix (Keys f F) (Keys c F) ℂ
variable {E J D: Type}  [Fintype D]
local notation "A"=> Modes f F
local notation "B"=> Modes c F
local notation "R"=> Junta c f F

-- explicit positions
abbrev ha (c : Side)(f:Side)(F:ℕ): Keys f F ↪ Junta c f F:= head ..
abbrev hb (c:Side)(f:Side)(F:ℕ): Keys c F↪ Junta c f F:= tail ..
def jointP (S: Ratio c f) : Junta c f F→ Site f:=Sum.elim (Sum.elim (fun i:A=> locationP (.inl i)) (fun i:B=> S.embed (locationP (.inl i)))) (Sum.elim (fun i:A=> locationP (.inr i)) (fun i:B=> S.embed (locationP (.inr i))))
lemma rootA (i:Keys f F): jointP S (ha c f F i)=locationP i:=by cases i <;> rfl
lemma rootB (i: Keys c F): jointP S (hb c f F i)=S.embed (locationP i):=by cases i <;> rfl

def hooks (S: Ratio c f)(U:Support f): Finset (Junta c f F):= univ.filter fun i=> jointP S i ∈ U
lemma hooked (i:Junta c f F)(U: Support f): i∈hooks S U↔ jointP S i ∈U:= by simp only [hooks,mem_filter,mem_univ,true_and]

def ahead (S : Ratio c f) (F:ℕ): EvenA f F→ₐ[ℂ] Patio (Junta c f F):= car (near _ _) (fun x he=> (embed_grade _ x).trans (congr_arg _ he))

-- always finite D indexing optional operators excess (fixed analytic radius). Short mask b reads via spoon, posture. Require selected A0 property.
structure Send (T:Ratio c f) (F:ℕ) (D:Type) where
 rooms : D→Support f
 trim : ℕ
 shortP : Grid f→ Water c f F
 treats : D→Grid f → EndA (Junta c f F)
 hat (U i j): Commute (treats i U) (treats j U)
 weld U i: Stays (excess (treats i U)) (hooks T (rooms i))
 fuel U i: excess (treats i U) 1=0
 stance i: LocalOn (rooms i) (treats i)
 shortens (i : Keys f F)(j: Keys c F) : LocalOn (halo trim {locationP i}) (fun U=> shortP U i j)
 sleeps (i : Keys f F)(j: Keys c F)(U : Grid f): shortP U i j≠0 → T.embed (locationP j)∈halo trim {locationP i}
 vibe : Continuous shortP
 river : ∀ i,Continuous (treats i)

-- reader on every field
namespace Send
variable (g:Send S F D)

def accord (P: Ratio c f)(F:ℕ)(Y: Water c f F): Patio (Junta c f F) →ₐ[ℂ] EvenA c F:=car (wipe _ _ Y) (fun x he=> (exterior_parity _ x).trans (congr_arg _ he))

def Cast (Q : Grid f→ Matrix B A ℂ) (H: Grid f→ Matrix A A ℂ) :Prop:=∀ U,birth (∑ i,g.treats i U)=birth (bark (bladesF ((H U)⁻¹*(Q U)ᴴ) (Q U*(H U)⁻¹)-g.shortP U)) * birth (pond (head A B) (H U)⁻¹)

lemma drum (Q:Grid f→Matrix B A ℂ)(D₀: Grid f→ Matrix A A ℂ)(h: g.Cast Q (fun U=>D₀ U+(Q U)ᴴ*Q U))(U:Grid f)(x:Fields f F) (hp : IsUnit ((D₀ U)+(Q U)ᴴ*Q U).det):
   let H := D₀ U+(Q U)ᴴ*Q U
   sheath 1 (Q U) (gauss (D₀ U) * x)= H.det • (wipe A B (g.shortP U) (birth (∑ i,g.treats i U) (near A B x))*gauss (1-Q U*H⁻¹*(Q U)ᴴ)) := by
  intro H₀; rw [clothe]; simp only [joinD, Complex.ofReal_one,one_smul, inv_one, one_pow]; simp only [neg_smul, one_smul]
  rw [asset _ hp _ _ (g.shortP U) _ _]
  have hh:=h U
  change H₀.det • _ = H₀.det • _; dsimp only at hh; rw [hh]
  simp only [Matrix.neg_mul,Matrix.mul_neg,neg_neg]; rfl

end Send
end YM.QCD.Cove
