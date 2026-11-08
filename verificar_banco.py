
import sqlite3
from pathlib import Path

PASTA = Path(__file__).resolve().parent
BANCO = PASTA / "aps_biometria.db"

if not BANCO.exists():
    print("ERRO: Banco de dados não encontrado:", BANCO)
    raise SystemExit

conexao = sqlite3.connect(
    f"{BANCO.as_uri()}?mode=ro",
    uri=True
)

try:
    print("=== TABELAS DO BANCO ===")

    tabelas = conexao.execute("""
        SELECT name
        FROM sqlite_master
        WHERE type = 'table'
        ORDER BY name
    """).fetchall()

    for (tabela,) in tabelas:
        print(f"\n--- {tabela} ---")

        colunas = conexao.execute(
            f'PRAGMA table_info("{tabela}")'
        ).fetchall()

        for coluna in colunas:
            print(
                f"Nome: {coluna[1]} | "
                f"Tipo: {coluna[2]} | "
                f"Obrigatório: {bool(coluna[3])}"
            )

    print("\nVerificação concluída. Nenhuma alteração realizada.")

finally:
    conexao.close()
