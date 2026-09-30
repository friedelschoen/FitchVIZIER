use std::collections::HashMap;
use std::sync::RwLock;

use clap::Parser;
use tower_lsp_server::jsonrpc::Result;
use tower_lsp_server::ls_types::*;
use tower_lsp_server::{Client, LanguageServer, LspService, Server};

#[derive(Parser)]
struct Args {
    #[arg(long, action)]
    debug: bool,
}

#[derive(Debug)]
struct Document {
    text: String,
}

#[derive(Debug)]
struct Backend {
    client: Client,
    documents: RwLock<HashMap<Uri, Document>>,
}

fn span_to_range(span: fitch_proof::Span) -> Range {
    let fitch_proof::Span { start, end } = span;
    Range {
        start: Position {
            line: start.line.saturating_sub(1) as u32,
            character: start.column.saturating_sub(1) as u32,
        },
        end: Position {
            line: end.line.saturating_sub(1) as u32,
            character: end.column.saturating_sub(1) as u32,
        },
    }
}

fn diagnostic_to_lsp(uri: &Uri, result: fitch_proof::ProofResult) -> Vec<Diagnostic> {
    fn convert(
        uri: &Uri,
        diag: fitch_proof::Diagnostic,
        severity: DiagnosticSeverity,
    ) -> Diagnostic {
        let fitch_proof::Diagnostic {
            message,
            span,
            related,
        } = diag;

        let related_information = (!related.is_empty()).then(|| {
            related
                .into_iter()
                .map(|relation| DiagnosticRelatedInformation {
                    location: Location {
                        uri: uri.clone(),
                        range: span_to_range(relation.span),
                    },
                    message: relation.message,
                })
                .collect()
        });

        Diagnostic {
            range: span_to_range(span),
            severity: Some(severity),
            source: Some("fitchvizier".into()),
            message,
            related_information,
            ..Default::default()
        }
    }

    match result {
        fitch_proof::ProofResult::Correct(span) => vec![Diagnostic {
            range: span_to_range(span),
            severity: Some(DiagnosticSeverity::INFORMATION),
            source: Some("fitchvizier".into()),
            message: "Proof is valid".into(),
            ..Default::default()
        }],

        fitch_proof::ProofResult::FatalError(diag) => {
            vec![convert(uri, diag, DiagnosticSeverity::ERROR)]
        }

        fitch_proof::ProofResult::Error(diags) => diags
            .into_iter()
            .map(|diag| convert(uri, diag, DiagnosticSeverity::WARNING))
            .collect(),
    }
}

fn end_position(text: &str) -> Position {
    let mut lines = text.split('\n');
    let mut line = 0;
    let mut last = "";

    while let Some(current) = lines.next() {
        last = current;

        if lines.clone().next().is_some() {
            line += 1;
        }
    }

    Position::new(line, last.encode_utf16().count() as u32)
}

impl Backend {
    fn new(client: Client) -> Self {
        Self {
            client,
            documents: RwLock::new(HashMap::new()),
        }
    }
}

impl LanguageServer for Backend {
    async fn initialize(&self, _: InitializeParams) -> Result<InitializeResult> {
        Ok(InitializeResult {
            capabilities: ServerCapabilities {
                text_document_sync: Some(TextDocumentSyncCapability::Kind(
                    TextDocumentSyncKind::FULL,
                )),

                document_formatting_provider: Some(OneOf::Left(true)),

                diagnostic_provider: Some(DiagnosticServerCapabilities::Options(
                    DiagnosticOptions {
                        identifier: Some("fitchvizier".into()),
                        inter_file_dependencies: false,
                        workspace_diagnostics: false,
                        ..Default::default()
                    },
                )),

                ..Default::default()
            },

            server_info: Some(ServerInfo {
                name: "fitchvizier-lsp".into(),
                version: None,
            }),

            offset_encoding: None,
        })
    }

    async fn initialized(&self, _: InitializedParams) {
        self.client
            .log_message(MessageType::INFO, "server initialized!")
            .await;
    }

    async fn did_open(&self, params: DidOpenTextDocumentParams) {
        let doc = params.text_document;

        self.documents
            .write()
            .unwrap()
            .insert(doc.uri, Document { text: doc.text });
    }

    async fn did_change(&self, params: DidChangeTextDocumentParams) {
        let Some(change) = params.content_changes.into_iter().last() else {
            return;
        };

        self.documents
            .write()
            .unwrap()
            .insert(params.text_document.uri, Document { text: change.text });
    }

    async fn did_close(&self, params: DidCloseTextDocumentParams) {
        self.documents
            .write()
            .unwrap()
            .remove(&params.text_document.uri);
    }

    async fn diagnostic(
        &self,
        params: DocumentDiagnosticParams,
    ) -> Result<DocumentDiagnosticReportResult> {
        let documents = self.documents.read().unwrap();

        let diagnostics = documents
            .get(&params.text_document.uri)
            .iter()
            .map(|document| {
                fitch_proof::check_proof_diagnostics(
                    &document.text,
                    fitch_proof::DEFAULT_ALLOWED_VARIABLE_NAMES,
                )
            })
            .flat_map(|d| diagnostic_to_lsp(&params.text_document.uri, d))
            .collect();

        Ok(DocumentDiagnosticReportResult::Report(
            DocumentDiagnosticReport::Full(RelatedFullDocumentDiagnosticReport {
                related_documents: None,

                full_document_diagnostic_report: FullDocumentDiagnosticReport {
                    result_id: None,
                    items: diagnostics,
                },
            }),
        ))
    }

    async fn formatting(&self, params: DocumentFormattingParams) -> Result<Option<Vec<TextEdit>>> {
        let documents = self.documents.read().unwrap();

        let Some(document) = documents.get(&params.text_document.uri) else {
            return Ok(None);
        };

        let formatted = fitch_proof::format_proof(&document.text);

        if formatted == "invalid" || formatted == document.text {
            return Ok(None);
        }

        Ok(Some(vec![TextEdit {
            range: Range {
                start: Position::new(0, 0),
                end: end_position(&document.text),
            },
            new_text: formatted,
        }]))
    }

    async fn shutdown(&self) -> Result<()> {
        Ok(())
    }
}

#[tokio::main]
async fn main() {
    let stdin = tokio::io::stdin();
    let stdout = tokio::io::stdout();

    let (service, socket) = LspService::new(Backend::new);
    Server::new(stdin, stdout, socket).serve(service).await;
}
